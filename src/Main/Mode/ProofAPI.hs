{-# LANGUAGE FieldSelectors #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
-- | JSON-lines interface to manual, native Tamarin proof construction.
module Main.Mode.ProofAPI (proofAPIMode) where

import Control.DeepSeq (force)
import Control.Exception hiding (handle)
import Control.Monad (unless, when)
import Control.Monad.Trans.Except (runExceptT)
import Data.Aeson
import Data.Aeson.Types (Pair, Parser, parseEither)
import Data.ByteString qualified as BS
import Data.ByteString.Lazy qualified as BL
import Data.Label qualified as L
import Data.List (foldl', intercalate, isPrefixOf)
import Data.Map.Strict qualified as M
import Data.Monoid (Any (..))
import Data.Maybe (fromMaybe, isNothing)
import GHC.IO.Handle (hDuplicate, hDuplicateTo)
import Main.Console
import Main.TheoryLoader qualified as Loader
import System.Console.CmdArgs.Explicit
import System.Directory (removeFile, renameFile)
import System.FilePath (takeDirectory, takeFileName)
import System.IO
import Text.PrettyPrint.Class (render)
import Theory
import Theory.Constraint.Solver.Goals (openGoals)
import Theory.Tools.Wellformedness (prettyWfErrorReport)

-- The original open theory is deliberately retained: opening a closed SAPIC
-- theory alone would save its translation instead of the user's definitions.
data Session = Session
  { sourceTheory :: OpenTheory
  , currentTheory :: ClosedTheory
  , selectedLemma :: Maybe String
  , cursors :: M.Map String ProofPath
  , cachedMethods :: [ProofMethod]
  , undoHistory :: [Mutation]
  , redoHistory :: [Mutation]
  }

-- History contains only immutable engine/view state, never another Session or
-- its history stacks. Native theories and proofs are shared, not copied.
-- Strict fields also prevent selector thunks from retaining an old Session.
data Snapshot = Snapshot
  !ClosedTheory !(Maybe String) !(M.Map String ProofPath) ![ProofMethod]

data Mutation = Mutation !Snapshot !Snapshot

data Request = Request String (Maybe String) (Maybe Int) (Maybe Integer)

proofAPIMode :: TamarinMode
proofAPIMode = tamarinMode "proof-api"
  "Serve manual proof operations as JSON lines on standard input/output."
  setup runAPI
  where
    setup m = m
      { modeCheck = updateArg "mode" "proof-api"
      , modeGroupFlags = Group
          [flagOpt "maude" ["with-maude"] (updateArg "withMaude") "FILE"
             "Path to the Maude executable."] [] [("About", [helpFlag])]
      }

-- Keep a dedicated copy of the protocol handle. All ordinary stdout writes,
-- including lazy solver/oracle output, go to stderr for the entire session.
runAPI :: TamarinMode -> Arguments -> IO ()
runAPI _ args = bracket (hDuplicate stdout) hClose $ \protocol -> do
  hSetBuffering protocol LineBuffering
  hDuplicateTo stderr stdout
  hSetBuffering stdout LineBuffering
  loop protocol 0 Nothing
  where
    opts = Loader.defaultTheoryLoadOptions
      { Loader.maudePath = maudePath args }
    -- Revisions belong to the protocol session, not restorable proof history.
    loop protocol revision session = do
      eof <- hIsEOF stdin
      unless eof $ do
        line <- BS.hGetLine stdin
        outcome <- try $ do
          request <- either apiError pure $ eitherDecodeStrict' line >>= parseEither parseRequest
          (next, response, stop) <- dispatch opts revision session request
          let nextRevision = if changesRevision request then revision + 1 else revision
          -- Force both the new engine state and the complete response before
          -- committing: a lazy Maude/pretty-printer exception is an error reply,
          -- not a half JSON line or a corrupted session.
          case next of
            Nothing -> pure ()
            Just s -> do
              _ <- evaluate (force (currentTheory s))
              _ <- evaluate (force (cachedMethods s))
              pure ()
          bytes <- evaluate (force (encode (success nextRevision response)))
          pure (next, nextRevision, bytes, stop)
        case outcome of
          Left (e :: SomeException) -> case fromException e :: Maybe AsyncException of
            Just a -> throwIO a
            Nothing -> do
              BL.hPutStr protocol $ encode $ object
                ["status" .= ("error" :: String), "message" .= displayException e,
                 "revision" .= revision]
              BS.hPutStr protocol "\n"
              hFlush protocol
              loop protocol revision session
          Right (next, nextRevision, bytes, stop) -> do
            BL.hPutStr protocol bytes
            BS.hPutStr protocol "\n"
            hFlush protocol
            unless stop $ loop protocol nextRevision next

parseRequest :: Value -> Parser Request
parseRequest = withObject "request" $ \o -> do
  command <- o .: "command"
  case command :: String of
    "load" -> Request command . Just <$> o .: "file" <*> pure Nothing <*> pure Nothing
    "save" -> Request command . Just <$> o .: "file" <*> pure Nothing <*> pure Nothing
    "lemma" -> Request command . Just <$> o .: "name" <*> pure Nothing <*> pure Nothing
    "apply" -> Request command Nothing . Just <$> o .: "method_id"
      <*> (Just <$> o .: "expected_revision")
    "step" -> Request "apply" Nothing . Just <$> o .: "method_id"
      <*> (Just <$> o .: "expected_revision")
    "branch" -> Request command Nothing . Just <$> o .: "branch_id" <*> pure Nothing
    _ -> pure $ Request command Nothing Nothing Nothing

changesRevision :: Request -> Bool
changesRevision (Request command _ _ _) = command `elem`
  ["load", "lemma", "branch", "back", "apply", "reset", "undo", "redo", "check"]

apiError :: String -> IO a
apiError = ioError . userError

require :: String -> Maybe a -> IO a
require message = maybe (apiError message) pure

success :: Integer -> [Pair] -> Value
success revision fields = object $
  ["status" .= ("success" :: String), "revision" .= revision] ++ fields

-- A failed operation never installs its candidate Session in the loop.
dispatch :: Loader.TheoryLoadOptions -> Integer -> Maybe Session -> Request
         -> IO (Maybe Session, [Pair], Bool)
dispatch opts revision previous (Request command text index expectedRevision)
  | command == "apply" && expectedRevision /= Just revision =
      apiError "Stale expected_revision; refresh state or methods before applying a method"
  | command == "quit" = pure (previous, [], True)
  | command == "load" = do
      file <- require "Missing file" text
      contents <- readFile file
      _ <- evaluate (force contents)
      loaded <- runExceptT $ Loader.loadTheory opts contents file
      original <- case loaded of
        Left e -> apiError (show e)
        Right (Right _) -> apiError "Diff/equivalence theories are not supported by proof-api; use the GUI."
        Right (Left thy) -> evaluate (force thy)
      sig <- toSignatureWithMaude opts.maudePath (L.get thySignature original)
      closed <- runExceptT $ Loader.closeTheory "" opts sig (Left original)
      thy <- case closed of
        Left e -> apiError (show e)
        Right (_, Right _) -> apiError "Diff/equivalence theories are not supported by proof-api."
        Right (warnings, Left t) -> do
          unless (null warnings) $
            hPutStrLn stderr $ "WARNING: theory wellformedness checks failed:\n"
              ++ render (prettyWfErrorReport warnings)
          pure t
      let session = Session original thy Nothing M.empty [] [] []
      pure (Just session,
        ["theory" .= L.get thyName thy, "file" .= file, "lemmas" .= lemmaValues thy], False)
  | otherwise = do
      session <- require "No theory loaded; use load first" previous
      case command of
        "lemmas" -> unchanged session ["lemmas" .= lemmaValues (currentTheory session)]
        "lemma" -> do
          name <- require "Missing lemma name" text
          _ <- require "No such lemma" $ lookupLemma name (currentTheory session)
          next <- refresh session { selectedLemma = Just name }
          selected next []
        "save" -> do
          file <- require "Missing file" text
          let saved = nativeTheory session
              contents = render (prettyOpenTheory saved) ++ "\n"
          _ <- evaluate (force contents)
          atomicSave file contents
          unchanged session ["file" .= file]
        "state" -> selected session []
        "methods" -> do
          _ <- selection session
          unchanged session ["methods" .= methodValues session]
        "goals" -> do
          (_, _, _, node) <- selection session
          unchanged session ["goals" .= goalValues node]
        "branches" -> do
          (_, proof, path, node) <- selection session
          unchanged session ["branches" .= branchValues proof path node]
        "branch" -> do
          (name, _, path, node) <- selection session
          i <- require "Missing branch_id" index
          (caseName, _) <- require "Invalid branch index" $ atIndex i (M.toList (children node))
          next <- refresh session { cursors = M.insert name (path ++ [caseName]) (cursors session) }
          selected next []
        "back" -> do
          (name, _, path, _) <- selection session
          when (null path) $ apiError "Already at the proof root"
          next <- refresh session { cursors = M.insert name (init path) (cursors session) }
          selected next []
        "apply" -> do
          (name, proof, path, node) <- selection session
          unless (isSorry node && M.null (children node)) $
            apiError "This node already contains a proof step or retained subproof; use reset before replacing it"
          i <- require "Missing method_id" index
          method <- require "Invalid method index" $ atIndex i (cachedMethods session)
          sys <- require "No annotated proof state at this node" $ psInfo (root node)
          lemma <- require "No such lemma" $ lookupLemma name (currentTheory session)
          let ctxt = getProofContext lemma (currentTheory session)
          proof' <- require "The selected proof method failed" $
            modifyAtPath (runProver (oneStepProver method) ctxt (length path) sys) path proof
          installed <- installProof session name proof'
          (_, installedProof, _, appliedNode) <- selection installed
          let generated = branchValues installedProof path appliedNode
          navigated <- case M.toList (children appliedNode) of
            [(caseName, _)] -> refresh installed
              { cursors = M.insert name (path ++ [caseName]) (cursors installed) }
            _ -> pure installed
          let next = rememberMutation session navigated
          selected next
            [ "applied" .= render (prettyProofMethod method)
            , "applied_at" .= nodeId installedProof path
            , "generated_branches" .= generated
            ]
        "undo" -> case undoHistory session of
          [] -> apiError "There is no mutation to undo"
          change@(Mutation before _) : rest -> do
            let next = (restoreSnapshot before session)
                  { undoHistory = rest, redoHistory = change : redoHistory session }
            selected next []
        "redo" -> case redoHistory session of
          [] -> apiError "There is no mutation to redo"
          change@(Mutation _ after) : rest -> do
            let next = (restoreSnapshot after session)
                  { undoHistory = change : undoHistory session, redoHistory = rest }
            selected next []
        "reset" -> do
          (name, proof, path, node) <- selection session
          when (isSorry node && M.null (children node)) $
            apiError "This node is already an empty sorry"
          proof' <- require "Invalid proof path" $
            modifyAtPath (\p -> Just $ sorry Nothing (psInfo (root p))) path proof
          installed <- installProof session name proof'
          selected (rememberMutation session installed) []
        "tree" -> do
          (name, proof, _, _) <- selection session
          unchanged session ["lemma" .= name, "tree" .= treeValue "0" name proof]
        "check" -> do
          (name, _, _, _) <- selection session
          -- Replay only recorded steps. New or unfinished cases remain sorry;
          -- no automatic prover or extra simplify operation is run.
          let replayed = replay (currentTheory session)
          next <- refresh session { currentTheory = replayed }
          lemma <- require "No such lemma" $ lookupLemma name replayed
          let (result, message) = checkedResult replayed lemma
          pure (Just next,
            ["lemma" .= name, "result" .= result, "message" .= message], False)
        _ -> apiError $ "Unknown command: " ++ command
  where
    unchanged session response = pure (Just session, response, False)
    selected session extra = do
      fields <- stateFields session
      unchanged session (fields ++ extra)

atIndex :: Int -> [a] -> Maybe a
atIndex i _ | i < 0 = Nothing
atIndex i xs = case drop i xs of
  x : _ -> Just x
  [] -> Nothing

selection :: Session -> IO (String, IncrementalProof, ProofPath, IncrementalProof)
selection session = do
  name <- require "No lemma selected; use lemma NAME" $ selectedLemma session
  lemma <- require "No such lemma" $ lookupLemma name (currentTheory session)
  let proof = L.get lProof lemma
      path = M.findWithDefault [] name (cursors session)
  node <- require "Invalid proof path" $ atPath proof path
  pure (name, proof, path, node)

refresh :: Session -> IO Session
refresh session = case selectedLemma session of
  Nothing -> pure session { cachedMethods = [] }
  Just name -> do
    lemma <- require "No such lemma" $ lookupLemma name (currentTheory session)
    let proof = L.get lProof lemma
        oldPath = M.findWithDefault [] name (cursors session)
        nearest p = case atPath proof p of
          Just found -> (p, found)
          Nothing -> nearest (init p)
        (path, node) = nearest oldPath
        ctxt = getProofContext lemma (currentTheory session)
        methods = case psInfo (root node) of
          Just sys | isSorry node && M.null (children node) ->
            let heuristic = fromMaybe (defaultHeuristic False) (L.get pcHeuristic ctxt)
                tactic = fromMaybe [defaultTactic] (L.get pcTactic ctxt)
            in map fst $ rankProofMethods (useHeuristic heuristic (length path)) tactic ctxt sys
          _ -> []
    _ <- evaluate (force methods)
    pure session { cursors = M.insert name path (cursors session), cachedMethods = methods }

replay :: ClosedTheory -> ClosedTheory
replay = proveTheory (const True) (checkAndExtendProver (sorryProver Nothing))

installProof :: Session -> String -> IncrementalProof -> IO Session
installProof session name proof = do
  thy <- require "Could not replace lemma proof" $ modifyLemma
    (\lemma -> if L.get lName lemma == name then L.set lProof proof lemma else lemma)
    (currentTheory session)
  -- Rebuild all proof annotations in declaration order, including subsequent
  -- reuse/source contexts. Native checking retains invalidated old subtrees.
  refresh session { currentTheory = replay thy }

isSorry :: IncrementalProof -> Bool
isSorry node = case psMethod (root node) of
  Sorry _ -> True
  _ -> False

snapshot :: Session -> Snapshot
snapshot session = Snapshot (currentTheory session) (selectedLemma session)
  (cursors session) (cachedMethods session)

restoreSnapshot :: Snapshot -> Session -> Session
restoreSnapshot (Snapshot thy lemma paths methods) session = session
  { currentTheory = thy, selectedLemma = lemma, cursors = paths
  , cachedMethods = methods
  }

rememberMutation :: Session -> Session -> Session
rememberMutation before after =
  let change = Mutation (snapshot before) (snapshot after)
  in change `seq` after
    { undoHistory = change : undoHistory before, redoHistory = [] }

nodeId :: IncrementalProof -> ProofPath -> String
nodeId proof = go "0" proof
  where
    go ident _ [] = ident
    go ident node (name : rest) = case lookup name
      [(n, (i, child)) | (i, (n, child)) <- zip [0 :: Int ..] (M.toList (children node))] of
        Nothing -> ident
        Just (i, child) -> go (ident ++ "." ++ show i) child rest

branchStatus :: IncrementalProof -> String
branchStatus proof
  | getAny invalid = "invalid"
  | getAny unfinished = "open"
  | otherwise = case psMethod (root proof) of
      Finished Solved -> "solved"
      Finished (Contradictory _) -> "contradictory"
      Finished Unfinishable -> "unfinishable"
      _ -> case status of
        CompleteProof -> "complete"
        TraceFound -> "solved"
        InvalidatedProof -> "invalid"
        UnfinishableProof -> "unfinishable"
        _ -> "open"
  where
    -- A witness in one child must not hide unfinished sibling branches.
    (invalid, unfinished, status) = foldProof summarize proof
    summarize step =
      ( Any (isNothing (psInfo step) || psMethod step == Invalidated)
      , Any (case psMethod step of Sorry _ -> True; _ -> False)
      , proofStepStatus step
      )

methodValues :: Session -> [Value]
methodValues session =
  [object ["id" .= i, "text" .= render (prettyProofMethod method)]
  | (i, method) <- zip [0 :: Int ..] (cachedMethods session)]

goalValues :: IncrementalProof -> [Value]
goalValues node = case psInfo (root node) of
  Nothing -> []
  Just sys -> [object ["id" .= i, "text" .= render (prettyGoal goal)]
              | (i, (goal, _)) <- zip [0 :: Int ..] (openGoals sys)]

branchValues :: IncrementalProof -> ProofPath -> IncrementalProof -> [Value]
branchValues proof path node =
  [object ["id" .= i, "name" .= name, "node_id" .= nodeId proof (path ++ [name]),
           "status" .= branchStatus child]
  | (i, (name, child)) <- zip [0 :: Int ..] (M.toList (children node))]

stateFields :: Session -> IO [Pair]
stateFields session = do
  (name, proof, path, node) <- selection session
  pure ["lemma" .= name, "node_id" .= nodeId proof path,
        "branch_status" .= branchStatus node,
        "state" .= maybe "No annotated constraint system (invalid or unreachable proof step)."
                     (render . prettySystem) (psInfo (root node)),
        "goals" .= goalValues node, "methods" .= methodValues session,
        "branches" .= branchValues proof path node]

treeValue :: String -> String -> IncrementalProof -> Value
treeValue ident name node = object
  ["node_id" .= ident, "name" .= name,
   "method" .= render (prettyProofMethod (psMethod (root node))),
   "status" .= branchStatus node,
   "children" .= [treeValue (ident ++ "." ++ show i) caseName child
                 | (i, (caseName, child)) <- zip [0 :: Int ..] (M.toList (children node))]]

lemmaValues :: ClosedTheory -> [Value]
lemmaValues thy =
  let results = resultTable thy
  in [object ["name" .= L.get lName lemma,
              "status" .= fst (results M.! L.get lName lemma)]
     | lemma <- theoryLemmas thy]

-- A sorry anywhere is never reported verified, even when a separate branch
-- contains an existential witness. Invalid/unreachable retained steps are
-- reported separately from genuinely unfinished proofs.
checkedResult :: ClosedTheory -> Lemma IncrementalProof -> (String, String)
checkedResult thy lemma = resultTable thy M.! L.get lName lemma

-- Compute prerequisite results once in declaration order, rather than
-- recursively replaying a shared chain of reuse dependencies for each lemma.
resultTable :: ClosedTheory -> M.Map String (String, String)
resultTable thy = foldl' add M.empty (theoryLemmas thy)
  where
    add results lemma = M.insert (L.get lName lemma) (localResult thy results lemma) results

localResult :: ClosedTheory -> M.Map String (String, String)
            -> Lemma IncrementalProof -> (String, String)
localResult thy results lemma
  | any invalid nodes = ("invalid", "Proof contains an invalid or unreachable step")
  | any isSorry nodes = ("incomplete", "Proof contains unfinished sorry branches")
  | not (null blockers) = ("incomplete", "Unverified reusable/source lemmas: " ++ intercalate ", " blockers)
  | otherwise = case foldProof proofStepStatus proof of
      CompleteProof -> if L.get lTraceQuantifier lemma == AllTraces
        then ("verified", "verified") else ("falsified", "falsified - no trace found")
      TraceFound -> if L.get lTraceQuantifier lemma == ExistsTrace
        then ("verified", "verified - found trace") else ("falsified", "falsified - found trace")
      _ -> ("incomplete", "Proof analysis cannot be finished")
  where
    proof = L.get lProof lemma
    nodes = allNodes proof
    invalid node = isNothing (psInfo (root node)) || psMethod (root node) == Invalidated
      || case psMethod (root node) of
           Sorry (Just reason) -> "invalid proof step" `isPrefixOf` reason
           _ -> False
    ctxt = getProofContext lemma thy
    hidden = L.get pcHiddenLemmas ctxt
    blockers = [L.get lName prior
      | prior <- takeWhile ((/= L.get lName lemma) . L.get lName) (theoryLemmas thy)
      , (SourceLemma `elem` L.get lAttributes prior && SourceLemma `notElem` L.get lAttributes lemma) ||
          (ReuseLemma `elem` L.get lAttributes prior && L.get lTraceQuantifier prior == AllTraces
           && (SourceLemma `elem` L.get lAttributes prior || SourceLemma `notElem` L.get lAttributes lemma)
           && L.get lName prior `notElem` hidden && "ALL" `notElem` hidden)
      , maybe True ((/= "verified") . fst) (M.lookup (L.get lName prior) results)]

allNodes :: IncrementalProof -> [IncrementalProof]
allNodes node = node : concatMap allNodes (M.elems (children node))

nativeTheory :: Session -> OpenTheory
nativeTheory session = original { _thyItems = map update (L.get thyItems original) ++ generated }
  where
    original = sourceTheory session
    opened = openTheory (currentTheory session)
    update (LemmaItem lemma) = case lookupLemma (L.get lName lemma) opened of
      Just current -> LemmaItem (L.set lProof (L.get lProof current) lemma)
      Nothing -> LemmaItem lemma
    update item = item
    -- Translations or explicit auto-sources may introduce additional lemmas.
    -- Keep those proofs too, without duplicating translated rules/processes.
    generated = [LemmaItem lemma | lemma <- theoryLemmas opened,
                  isNothing (lookupLemma (L.get lName lemma) original)]

atomicSave :: FilePath -> String -> IO ()
atomicSave file contents = bracketOnError
  (openTempFile (takeDirectory file) (takeFileName file ++ ".tmp"))
  (\(temporary, handle) -> do
      hClose handle `catch` (\(_ :: IOException) -> pure ())
      removeFile temporary `catch` (\(_ :: IOException) -> pure ()))
  (\(temporary, handle) -> do
      hPutStr handle contents
      hClose handle
      renameFile temporary file)
