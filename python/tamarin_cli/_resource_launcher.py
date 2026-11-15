"""POSIX exec launcher: set limits in a fresh interpreter, never preexec_fn."""

import os
import resource
import sys


def main() -> None:
    cpu_seconds, max_file_bytes = map(int, sys.argv[1:3])
    command = sys.argv[3:]
    # CPU accounting persists across exec and accumulates over the session.
    # Keep a one-second hard-limit margin so SIGXCPU identifies exhaustion.
    for kind, soft, hard in (
        (resource.RLIMIT_CPU, cpu_seconds, cpu_seconds + 1),
        (resource.RLIMIT_FSIZE, max_file_bytes, max_file_bytes),
    ):
        _, inherited_hard = resource.getrlimit(kind)
        if inherited_hard != resource.RLIM_INFINITY:
            hard = min(hard, inherited_hard)
            soft = min(soft, hard)
        resource.setrlimit(kind, (soft, hard))
    os.execvpe(command[0], command, os.environ)


if __name__ == "__main__":
    main()
