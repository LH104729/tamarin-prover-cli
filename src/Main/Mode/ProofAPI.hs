{-# LANGUAGE FieldSelectors #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
-- | JSON-lines interface to native proof construction and cancellable search.
module Main.Mode.ProofAPI (proofAPIMode) where

import Control.Concurrent (Chan, ThreadId, forkIOWithUnmask, killThread, newChan, readChan, writeChan)
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
import Data.Sequence (Seq, ViewL (..), (|>))
import Data.Sequence qualified as Seq
import Data.Set qualified as S
import Data.Unique (Unique, newUnique)
import GHC.IO.Handle (hDuplicate, hDuplicateTo)
import Main.Console
import Main.TheoryLoader qualified as Loader
import System.Console.CmdArgs.Explicit
import System.Directory (removeFile, renameFile)
import System.FilePath (takeDirectory, takeFileName)
import System.IO
import System.IO.Error (isEOFError)
import System.Timeout (timeout)
import Text.Read (readMaybe)
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

data Detail = Compact | Goals | Full

data Request = Request String (Maybe String) (Maybe Int) (Maybe Integer)
  | AutoRequest (Maybe Integer)
  | ObserveRequest Detail
  | ApplyRequest Int Integer (Maybe Int)
  | GotoRequest String Integer

data APIError = APIError String String Bool String deriving Show

instance Exception APIError

type PreparedResponse = (Maybe Session, Integer, BL.ByteString, Bool)

data APIEvent
  = RequestEvent (Either String Request)
  | InputEnded
  | InputFailed SomeException
  | WorkerCompleted Unique (Either SomeException PreparedResponse)

proofAPIMode :: TamarinMode
proofAPIMode = tamarinMode "proof-api"
  "Serve native proof operations and cancellable search as JSON lines."
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
  events <- newChan
  bracket (forkIOWithUnmask $ \unmask -> unmask $ readRequests events)
    killThread $ \_ -> loop events protocol 0 Nothing Seq.empty
  where
    opts = Loader.defaultTheoryLoadOptions
      { Loader.maudePath = maudePath args }
    -- Only this loop commits sessions and writes protocol responses. The input
    -- reader stays live while workers evaluate private, cancellable candidates.
    loop events protocol revision session pending = do
      (event, rest) <- case Seq.viewl pending of
        EmptyL -> do
          event <- readChan events
          pure (event, pending)
        event :< rest -> pure (event, rest)
      case event of
        InputEnded -> pure ()
        InputFailed e -> throwIO e
        WorkerCompleted _ _ -> loop events protocol revision session rest
        RequestEvent (Right (Request "cancel" _ _ _)) ->
          loop events protocol revision session rest
        RequestEvent (Right request) | cancellable request -> do
          token <- newUnique
          completed <- bracket
            (forkIOWithUnmask $ \unmask -> do
              outcome <- try $ unmask $ case request of
                ApplyRequest _ _ (Just milliseconds) -> do
                  result <- timeout (milliseconds * 1000) $
                    prepareRequest opts revision session request
                  maybe (apiFailure "TIMEOUT" "Proof step exceeded timeout_ms" True "observe") pure result
                _ -> prepareRequest opts revision session request
              writeChan events $ WorkerCompleted token outcome)
            killThread $ \worker ->
              awaitWorker events worker token request revision session rest
          case completed of
            Nothing -> pure ()
            Just (outcome, queued) -> finish events protocol revision session queued outcome
        RequestEvent request -> do
          outcome <- try $ either
            (\message -> apiFailure "INVALID_REQUEST" message True "help")
            (prepareRequest opts revision session) request
          finish events protocol revision session rest outcome
    finish events protocol revision session pending outcome = case outcome of
      Left (e :: SomeException) -> case fromException e :: Maybe AsyncException of
        Just a | a /= HeapOverflow && a /= StackOverflow -> throwIO a
        _ -> do
          writeResponse protocol $ encode $ errorResponse revision e
          loop events protocol revision session pending
      Right (next, nextRevision, bytes, stop) -> do
        writeResponse protocol bytes
        unless stop $ loop events protocol nextRevision next pending

-- Cancel has no reply of its own, including when idle. Other pipelined
-- requests wait for the worker reply; EOF shuts down without committing it.
cancellable :: Request -> Bool
cancellable (AutoRequest _) = True
cancellable (ApplyRequest _ _ _) = True
cancellable _ = False

awaitWorker :: Chan APIEvent -> ThreadId -> Unique -> Request -> Integer -> Maybe Session
            -> Seq APIEvent
            -> IO (Maybe (Either SomeException PreparedResponse, Seq APIEvent))
awaitWorker events worker token request revision session pending = do
  event <- readChan events
  case event of
    InputEnded -> pure Nothing
    InputFailed e -> throwIO e
    WorkerCompleted completed outcome
      | completed == token -> pure $ Just (outcome, pending)
      | otherwise -> await
    RequestEvent (Right (Request "cancel" _ _ _)) -> do
      killThread worker
      -- throwTo waits for delivery, not worker termination. Wait for cleanup
      -- (including external solver/oracle processes) before reusing the session.
      settled <- waitCancelled pending
      case settled of
        Nothing -> pure Nothing
        Just queued -> do
          outcome <- try $ do
            case request of
              AutoRequest _ -> do
                original <- require "No theory loaded; use load first" session
                fields <- stateFields Compact original
                prepareResponse revision session
                  (fields ++ ["auto_steps" .= (0 :: Integer), "auto_reason" .= ("cancelled" :: String)])
                  False
              _ -> apiFailure "CANCELLED" "Proof step cancelled; proof unchanged" True "observe"
          pure $ Just (outcome, queued)
    RequestEvent _ -> awaitWorker events worker token request revision session (pending |> event)
  where
    await = awaitWorker events worker token request revision session pending
    waitCancelled queued = do
      event <- readChan events
      case event of
        InputEnded -> pure Nothing
        InputFailed e -> throwIO e
        WorkerCompleted completed _
          | completed == token -> pure $ Just queued
          | otherwise -> waitCancelled queued
        RequestEvent (Right (Request "cancel" _ _ _)) -> waitCancelled queued
        RequestEvent _ -> waitCancelled (queued |> event)

readRequests :: Chan APIEvent -> IO ()
readRequests events = do
  line <- try $ BS.hGetLine stdin
  case line of
    Left (e :: IOException)
      | isEOFError e -> writeChan events InputEnded
      | otherwise -> writeChan events $ InputFailed (toException e)
    Right bytes -> do
      writeChan events $ RequestEvent $
        eitherDecodeStrict' bytes >>= parseEither parseRequest
      readRequests events

writeResponse :: Handle -> BL.ByteString -> IO ()
writeResponse protocol bytes = do
  BL.hPutStr protocol bytes
  BS.hPutStr protocol "\n"
  hFlush protocol

prepareRequest :: Loader.TheoryLoadOptions -> Integer -> Maybe Session -> Request
               -> IO PreparedResponse
prepareRequest _ revision previous (AutoRequest steps) = do
  session <- require "No theory loaded; use load first" previous
  (next, count, reason) <- automatic steps session
  fields <- stateFields Compact next
  let nextRevision = if count > 0 then revision + 1 else revision
  prepareResponse nextRevision (Just next)
    (fields ++ ["auto_steps" .= count, "auto_reason" .= reason]) False
prepareRequest opts revision previous request = do
  (next, response, stop) <- dispatch opts revision previous request
  let nextRevision = if changesRevision request then revision + 1 else revision
  prepareResponse nextRevision next response stop

-- Force the complete candidate and reply before the main loop can commit
-- either. Lazy solver/pretty-printer failures leave the old session intact.
prepareResponse :: Integer -> Maybe Session -> [Pair] -> Bool -> IO PreparedResponse
prepareResponse revision next fields stop = do
  case next of
    Nothing -> pure ()
    Just session -> do
      _ <- evaluate (force (currentTheory session))
      _ <- evaluate (force (cachedMethods session))
      pure ()
  bytes <- evaluate (force (encode (success revision fields)))
  pure (next, revision, bytes, stop)

parseRequest :: Value -> Parser Request
parseRequest = withObject "request" $ \o -> do
  command <- o .: "command"
  case command :: String of
    "load" -> Request command . Just <$> o .: "file" <*> pure Nothing <*> pure Nothing
    "save" -> Request command . Just <$> o .: "file" <*> pure Nothing <*> pure Nothing
    "lemma" -> Request command . Just <$> o .: "name" <*> pure Nothing <*> pure Nothing
    "apply" -> parseApply o
    "step" -> parseApply o
    "goto" -> GotoRequest <$> o .: "node_id" <*> o .: "expected_revision"
    "observe" -> ObserveRequest <$> parseDetail o
    "state" -> ObserveRequest <$> parseDetail o
    "branch" -> Request command Nothing . Just <$> o .: "branch_id" <*> pure Nothing
    "auto" -> do
      steps <- o .:! "steps"
      when (maybe False (< 0) steps) $ fail "steps must be a nonnegative integer"
      pure $ AutoRequest steps
    _ -> pure $ Request command Nothing Nothing Nothing
  where
    parseApply o = do
      method <- o .: "method_id"
      revision <- o .: "expected_revision"
      milliseconds <- o .:! "timeout_ms"
      when (maybe False (\n -> n <= 0 || n > maxBound `div` 1000) milliseconds) $
        fail "timeout_ms must be a positive integer representable in microseconds"
      pure $ ApplyRequest method revision milliseconds
    parseDetail o = do
      detail <- o .:? "detail" .!= ("compact" :: String)
      case detail of
        "compact" -> pure Compact
        "goals" -> pure Goals
        "full" -> pure Full
        _ -> fail "detail must be compact, goals, or full"

changesRevision :: Request -> Bool
changesRevision (Request command _ _ _) = command `elem`
  ["load", "lemma", "branch", "back", "apply", "reset", "undo", "redo", "check"]
changesRevision (AutoRequest _) = False
changesRevision (ApplyRequest _ _ _) = True
changesRevision (GotoRequest _ _) = True
changesRevision (ObserveRequest _) = False

apiFailure :: String -> String -> Bool -> String -> IO a
apiFailure code message recoverable action =
  throwIO $ APIError code message recoverable action

apiError :: String -> IO a
apiError message = apiFailure "INVALID_STATE" message True "observe"

errorResponse :: Integer -> SomeException -> Value
errorResponse revision exception =
  let APIError code message recoverable action =
        case fromException exception of
          Just failure -> failure
          Nothing -> case fromException exception :: Maybe AsyncException of
            Just HeapOverflow -> APIError "RESOURCE_LIMIT" "Backend heap limit exceeded" False "restart"
            Just StackOverflow -> APIError "RESOURCE_LIMIT" "Backend stack limit exceeded" False "restart"
            _ -> case fromException exception :: Maybe IOException of
              Just _ -> APIError "IO_ERROR" (displayException exception) True "retry"
              Nothing -> APIError "ENGINE_ERROR" (displayException exception) True "observe"
  in object ["status" .= ("error" :: String), "revision" .= revision,
       "error" .= object ["code" .= code, "message" .= message,
         "recoverable" .= recoverable, "suggested_action" .= action]]

require :: String -> Maybe a -> IO a
require message = maybe (apiError message) pure

requireCode :: String -> String -> String -> Maybe a -> IO a
requireCode code message action = maybe (apiFailure code message True action) pure

success :: Integer -> [Pair] -> Value
success revision fields = object $
  ["status" .= ("success" :: String), "revision" .= revision] ++ fields

-- A failed operation never installs its candidate Session in the loop.
dispatch :: Loader.TheoryLoadOptions -> Integer -> Maybe Session -> Request
         -> IO (Maybe Session, [Pair], Bool)
dispatch _ _ _ (AutoRequest _) = apiError "Auto must run in its cancellable worker"
dispatch _ _ previous (ObserveRequest detail) = do
  session <- require "No theory loaded; use load first" previous
  fields <- stateFields detail session
  pure (previous, fields, False)
dispatch _ revision previous (GotoRequest ident expected) = do
  when (expected /= revision) $
    apiFailure "STALE_REVISION" "Proof tree revision changed; refresh node references" True "frontier"
  session <- require "No theory loaded; use load first" previous
  (name, proof, _, _) <- selection session
  path <- requireCode "INVALID_NODE" "No such proof node in the selected lemma" "frontier" $
    pathForNodeId proof ident
  next <- refresh session { cursors = M.insert name path (cursors session) }
  fields <- stateFields Compact next
  pure (Just next, fields, False)
dispatch opts revision previous (ApplyRequest method expected _) =
  dispatch opts revision previous (Request "apply" Nothing (Just method) (Just expected))
dispatch opts revision previous (Request command text index expectedRevision)
  | command == "apply" && expectedRevision /= Just revision =
      apiFailure "STALE_REVISION" "Stale expected_revision; refresh state or methods before applying a method" True "observe"
  | command == "quit" = pure (previous, [], True)
  | command == "load" = do
      file <- require "Missing file" text
      contents <- readFile file
      _ <- evaluate (force contents)
      loaded <- runExceptT $ Loader.loadTheory opts contents file
      original <- case loaded of
        Left e -> apiError (show e)
        Right (Right _) -> apiFailure "UNSUPPORTED_THEORY" "Diff/equivalence theories are not supported by proof-api; use the GUI." True "load"
        Right (Left thy) -> evaluate (force thy)
      sig <- toSignatureWithMaude opts.maudePath (L.get thySignature original)
      closed <- runExceptT $ Loader.closeTheory "" opts sig (Left original)
      thy <- case closed of
        Left e -> apiError (show e)
        Right (_, Right _) -> apiFailure "UNSUPPORTED_THEORY" "Diff/equivalence theories are not supported by proof-api." True "load"
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
        "methods" -> do
          (_, _, _, node) <- selection session
          unchanged session ["methods" .= methodValues session node]
        "goals" -> do
          (_, _, _, node) <- selection session
          unchanged session ["goals" .= goalValues node]
        "branches" -> do
          (_, proof, path, node) <- selection session
          unchanged session ["branches" .= branchValues proof path node]
        "frontier" -> do
          (name, proof, _, _) <- selection session
          unchanged session ["lemma" .= name, "frontier" .= frontierValues "0" proof]
        "branch" -> do
          (name, _, path, node) <- selection session
          i <- require "Missing branch_id" index
          (caseName, _) <- requireCode "INVALID_NODE" "Invalid branch index" "branches" $
            atIndex i (M.toList (children node))
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
          method <- requireCode "INVALID_METHOD" "Invalid method index" "methods" $
            atIndex i (cachedMethods session)
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
        _ -> apiFailure "INVALID_REQUEST" ("Unknown command: " ++ command) True "help"
  where
    unchanged session response = pure (Just session, response, False)
    selected session extra = do
      fields <- stateFields Compact session
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

-- A budget counts method applications across the entire selected subtree,
-- not proof depth. Recorded steps are traversed, never replaced. The private
-- candidate has no intermediate history entries and is committed only after
-- prepareResponse has forced both its theory and complete reply.
automatic :: Maybe Integer -> Session -> IO (Session, Integer, String)
automatic bound original = do
  (name, _, start, _) <- selection original
  if bound == Just 0
    then pure (original, 0, "step_limit")
    else do
      (candidate, count, reason) <- walk name original 0 [start]
      if count == 0
        then pure (original, count, reason)
        else do
          -- Keep the operation's subtree selected so another bounded auto
          -- resumes all of its remaining branches, not just the last leaf.
          anchored <- selectPath name start candidate
          pure (rememberMutation original anchored, count, reason)
  where
    walk name session count pending
      | maybe False (count >=) bound = pure (session, count, "step_limit")
      | otherwise = case pending of
          [] -> pure (session, count, "finished")
          path : rest -> do
            (_, proof, _, _) <- selection session
            case atPath proof path of
              Nothing -> walk name session count rest
              Just node
                | not (M.null (children node)) ->
                    walk name session count (childPaths path node ++ rest)
                | isSorry node, Just sys <- psInfo (root node) -> do
                    focused <- selectPath name path session
                    case cachedMethods focused of
                      -- Oracle stopping methods are sorry leaves too. Once
                      -- recorded, revisiting them must not consume another
                      -- step or make unbounded auto loop without progress.
                      [] -> walk name focused count rest
                      method : _
                        | method == psMethod (root node) ->
                            walk name focused count rest
                        | otherwise -> do
                            lemma <- require "No such lemma" $
                              lookupLemma name (currentTheory focused)
                            let ctxt = getProofContext lemma (currentTheory focused)
                            proof' <- require "The selected proof method failed" $
                              modifyAtPath
                                (runProver (oneStepProver method) ctxt (length path) sys)
                                path proof
                            installed <- installProof focused name proof'
                            (_, _, _, applied) <- selection installed
                            let count' = count + 1
                            count' `seq` walk name installed count'
                              (childPaths path applied ++ rest)
                | otherwise -> walk name session count rest
    selectPath name path session
      | M.lookup name (cursors session) == Just path = pure session
      | otherwise = refresh session { cursors = M.insert name path (cursors session) }
    childPaths path node = [path ++ [name] | name <- M.keys (children node)]

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

-- Numeric IDs are revision-local addresses, not the engine's case-name paths.
-- Require canonical decimal components so malformed IDs never alias a node.
pathForNodeId :: IncrementalProof -> String -> Maybe ProofPath
pathForNodeId proof ident = case components ident of
  "0" : rest -> descend proof rest
  _ -> Nothing
  where
    components value = case break (== '.') value of
      (part, []) -> [part]
      (part, _ : rest) -> part : components rest
    descend _ [] = Just []
    descend node (part : rest) = do
      i <- readMaybe part
      if show (i :: Int) /= part then Nothing else do
        (name, child) <- atIndex i (M.toList (children node))
        (name :) <$> descend child rest

frontierValues :: String -> IncrementalProof -> [Value]
frontierValues ident node
  | M.null (children node) =
      [object ["node_id" .= ident, "branch_status" .= branchStatus node,
               "goal_count" .= goalCount node] | isSorry node]
  | otherwise = concat
      [frontierValues (ident ++ "." ++ show i) child
      | (i, child) <- zip [0 :: Int ..] (M.elems (children node))]

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

methodValues :: Session -> IncrementalProof -> [Value]
methodValues session node =
  [object $ ["id" .= i, "text" .= render (prettyProofMethod method),
             "name" .= name, "kind" .= kind] ++ relatedGoal method
  | (i, method) <- zip [0 :: Int ..] (cachedMethods session)
  , let (name, kind) = methodMetadata method]
  where
    goalIds = M.fromList $ zip (nodeGoals node) [0 :: Int ..]
    relatedGoal (SolveGoal goal) =
      maybe [] (\i -> ["goal_id" .= ("g" ++ show i)]) $ M.lookup goal goalIds
    relatedGoal _ = []

methodMetadata :: ProofMethod -> (String, String)
methodMetadata Simplify = ("simplify", "simplification")
methodMetadata (SolveGoal _) = ("solve", "constraint_resolution")
methodMetadata Induction = ("induction", "induction")
methodMetadata (Finished _) = ("finished", "termination")
methodMetadata (Sorry _) = ("sorry", "admission")
methodMetadata Invalidated = ("invalidated", "invalidation")

nodeGoals :: IncrementalProof -> [Goal]
nodeGoals node = maybe [] (map fst . openGoals) (psInfo (root node))

goalCount :: IncrementalProof -> Int
goalCount = length . nodeGoals

goalValues :: IncrementalProof -> [Value]
goalValues node =
  [object ["id" .= i, "goal_id" .= ("g" ++ show i), "text" .= render (prettyGoal goal)]
  | (i, goal) <- zip [0 :: Int ..] (nodeGoals node)]

constraintValue :: System -> Value
constraintValue sys = object
  [ "formulas" .= map (render . prettyGuarded) (S.toList $ L.get sFormulas sys)
  , "equations" .= render (prettyEqStore $ L.get sEqStore sys)
  , "subterms" .= render (prettySubtermStore $ L.get sSubtermStore sys)
  , "ordering" .= map (render . prettyLess) (S.toList $ L.get sLessAtoms sys)
  , "last" .= fmap (render . prettyNodeId) (L.get sLastAtom sys)
  ]

branchValues :: IncrementalProof -> ProofPath -> IncrementalProof -> [Value]
branchValues proof path node =
  [object ["id" .= i, "name" .= name, "node_id" .= nodeId proof (path ++ [name]),
           "status" .= branchStatus child]
  | (i, (name, child)) <- zip [0 :: Int ..] (M.toList (children node))]

stateFields :: Detail -> Session -> IO [Pair]
stateFields detail session = do
  (name, proof, path, node) <- selection session
  let compact =
        ["lemma" .= name, "node_id" .= nodeId proof path,
         "branch_status" .= branchStatus node, "goal_count" .= goalCount node,
         "children_count" .= M.size (children node),
         "methods" .= methodValues session node, "branches" .= branchValues proof path node]
      goals = ["goals" .= goalValues node,
               "constraints" .= fmap constraintValue (psInfo (root node))]
      full = ["state" .= maybe "No annotated constraint system (invalid or unreachable proof step)."
                              (render . prettySystem) (psInfo (root node))]
  -- No prettySystem evaluation or full-state serialization on compact/goals paths.
  pure $ compact ++ case detail of
    Compact -> []
    Goals -> goals
    Full -> goals ++ full

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
