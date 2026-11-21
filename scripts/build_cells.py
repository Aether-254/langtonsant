"""Compile SingleBlackEarly cell modules with memory-aware scheduling.

Each cell module holds one `decide +kernel` certificate, compiled by its own `lean` process.
Scheduling (largest first):
  * estimated peak memory per cell: EST_SMALL MB if T <= 40000 else EST_LARGE MB;
  * a cell starts only if the running estimates plus its own stay within BUDGET_MB and the
    measured available memory minus its estimate stays above RESERVE_MB;
  * watchdog: if available memory drops below HARD_MIN_MB, the most recently started process
    is killed and its cell is re-queued at the end.
This does not change what is proved: each module is the same kernel check `lake build` runs.

  * timeout: a cell running longer than 4 * (T / 800 + 30) seconds is killed and written to
    LOG + ".slow" for a later single-process retry.

usage: python build_cells.py LEAN_BIN LIB_DIR LIST_FILE PARAMS_JSON BUDGET_MB RESERVE_MB HARD_MIN_MB MAXJOBS LOG
"""
import json
import os
import subprocess
import sys
import time

EST_SMALL = 1500
EST_LARGE = 3000


def free_mb():
    if os.name == "nt":
        out = subprocess.run(
            ["powershell", "-NoProfile", "-Command",
             "[int]((Get-CimInstance Win32_OperatingSystem).FreePhysicalMemory/1024)"],
            capture_output=True, text=True).stdout.strip()
        return int(out or 0)
    with open("/proc/meminfo") as f:
        for line in f:
            if line.startswith("MemAvailable:"):
                return int(line.split()[1]) // 1024
    return 0


def main():
    (lean, libdir, listfile, paramsfile, budget, reserve, hard_min, maxjobs, log) = sys.argv[1:10]
    budget, reserve, hard_min, maxjobs = int(budget), int(reserve), int(hard_min), int(maxjobs)
    params = json.load(open(paramsfile))
    queue = [int(x) for x in open(listfile).read().split()]
    outdir = os.path.join(libdir, "SingleBlackEarly")
    os.makedirs(outdir, exist_ok=True)
    env = dict(os.environ, LEAN_PATH=libdir)
    est = lambda k: EST_SMALL if params[k]["T"] <= 40000 else EST_LARGE
    queue = [k for k in queue if not os.path.exists(os.path.join(outdir, f"C{k:04d}.olean"))]
    running = {}  # k -> (proc, start, outfile)
    done = 0
    total = len(queue)
    logf = open(log, "a")

    def record(line):
        print(line, flush=True)
        logf.write(line + "\n")
        logf.flush()

    record(f"start: {total} cells queued")
    while queue or running:
        # reap finished
        for k in list(running):
            p, t0, outf = running[k]
            if p.poll() is not None:
                outf.close()
                name = f"C{k:04d}"
                olean = os.path.join(outdir, name + ".olean")
                msg = open(outf.name).read().strip().replace("\n", " | ")[:300]
                if p.returncode == 0:
                    os.replace(olean + ".tmp", olean)
                    done += 1
                record(f"cell {k:04d} exit {p.returncode} seconds {time.time() - t0:.0f} "
                       f"[{done}/{total}] {msg}")
                del running[k]
        # timeout
        for k in list(running):
            p, t0, outf = running[k]
            if time.time() - t0 > 4 * (params[k]["T"] / 800 + 30):
                p.kill(); p.wait(); outf.close()
                del running[k]
                with open(log + ".slow", "a") as sf:
                    sf.write(f"{k}\n")
                record(f"TIMEOUT cell {k:04d} after {time.time() - t0:.0f} s, moved to slow list")
        free = free_mb()
        # watchdog
        if running and free < hard_min:
            k = max(running, key=lambda k: running[k][1])
            running[k][0].kill()
            running[k][0].wait()
            running[k][2].close()
            del running[k]
            queue.append(k)
            record(f"WATCHDOG killed cell {k:04d} (free {free} MB), re-queued")
            time.sleep(5)
            continue
        # admit
        if queue and len(running) < maxjobs:
            k = queue[0]
            load = sum(est(j) for j in running)
            if load + est(k) <= budget and free - est(k) >= reserve:
                queue.pop(0)
                name = f"C{k:04d}"
                outf = open(os.path.join(outdir, name + ".log"), "w")
                p = subprocess.Popen(
                    [lean, "-DwarningAsError=true", "-o", os.path.join(outdir, name + ".olean.tmp"),
                     "-i", os.path.join(outdir, name + ".ilean"),
                     os.path.join("SingleBlackEarly", name + ".lean")],
                    env=env, stdout=outf, stderr=subprocess.STDOUT)
                running[k] = (p, time.time(), outf)
                time.sleep(3)
                continue
        time.sleep(2)
    record(f"finished: {done}/{total}")


if __name__ == "__main__":
    main()
