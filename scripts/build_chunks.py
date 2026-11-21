"""Compile SingleBlackEarly chunk files with bounded parallelism and one thread per file.

Lake cannot limit how many files it compiles at once, and Lean by default checks several
theorems of one file concurrently; together this exhausted memory.  This script runs
`lean -j1 -o ... -i ...` for the requested chunks with at most N concurrent processes and
records wall time and exit status per chunk.  It does not change what is proved: each chunk is
the same kernel check that `lake build` would run.

usage: python build_chunks.py LEAN_BIN LIB_DIR FIRST LAST JOBS LOG
"""
import os
import subprocess
import sys
import time
from concurrent.futures import ThreadPoolExecutor


def main():
    lean, libdir, first, last, jobs, log = sys.argv[1], sys.argv[2], int(sys.argv[3]), \
        int(sys.argv[4]), int(sys.argv[5]), sys.argv[6]
    outdir = os.path.join(libdir, "SingleBlackEarly")
    os.makedirs(outdir, exist_ok=True)
    env = dict(os.environ, LEAN_PATH=libdir)

    def one(i):
        name = f"Chunk{i:03d}"
        src = os.path.join("SingleBlackEarly", name + ".lean")
        olean = os.path.join(outdir, name + ".olean")
        if os.path.exists(olean):
            return i, 0, 0.0, "skip"
        t = time.time()
        p = subprocess.run([lean, "-j1", "-DwarningAsError=true", "-o", olean + ".tmp",
                            "-i", os.path.join(outdir, name + ".ilean"), src],
                           env=env, capture_output=True, text=True)
        dt = time.time() - t
        if p.returncode == 0:
            os.replace(olean + ".tmp", olean)
        msg = (p.stdout + p.stderr).strip().replace("\n", " | ")[:300]
        return i, p.returncode, dt, msg

    with open(log, "a") as f, ThreadPoolExecutor(max_workers=jobs) as ex:
        for i, code, dt, msg in ex.map(one, range(first, last + 1)):
            line = f"chunk {i:03d} exit {code} seconds {dt:.0f} {msg}"
            print(line, flush=True)
            f.write(line + "\n")
            f.flush()


if __name__ == "__main__":
    main()
