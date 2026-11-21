"""Write a Kaggle script kernel that runs native_decide block scans fastScan P 2^24 (2^24*k).

usage: python make_kernel.py OUTDIR SLUG P START COUNT
The kernel unpacks the private dataset aether254/lean-ant-bundle (Linux Lean toolchain + the 18
source modules), builds the precompiled checker, then builds PeriodicNative.P{P}B{k} modules in
small batches until 11 h have elapsed, and leaves their .olean/.ilean files in /kaggle/working.
"""
import json, os, sys

TEMPLATE = r'''
import glob, hashlib, os, shutil, subprocess, sys, tarfile, time
T0 = time.time()
P, START, COUNT = __P__, __START__, __COUNT__
LIMIT = 11.0 * 3600
W = 2 ** 24
OUT = "/kaggle/working"
logf = open(os.path.join(OUT, "log.txt"), "a")
def say(*a):
    msg = "[%7.0fs] " % (time.time() - T0) + " ".join(str(x) for x in a)
    print(msg, flush=True); logf.write(msg + "\n"); logf.flush()

def find(pattern):
    hits = glob.glob("/kaggle/input/**/" + pattern, recursive=True)
    return hits[0] if hits else None

say("job", P, START, COUNT, "nproc", os.cpu_count())
tool = find("lean-4.36.0-linux/bin/lean")
if tool:
    root = os.path.dirname(os.path.dirname(tool))
    shutil.copytree(root, "/tmp/lean-4.36.0-linux", symlinks=True)
else:
    arch = find("lean-tool.tar.xz")
    say("extracting", arch)
    subprocess.run(["tar", "-xJf", arch, "-C", "/tmp"], check=True)
projtar = find("proj.tar")
if projtar:
    subprocess.run(["tar", "-xf", projtar, "-C", "/tmp"], check=True)
else:
    shutil.copytree(os.path.dirname(find("proj/lakefile.toml")), "/tmp/proj")
os.environ["PATH"] = "/tmp/lean-4.36.0-linux/bin:" + os.environ["PATH"]
os.chdir("/tmp/proj")
say(subprocess.run(["lean", "--version"], capture_output=True, text=True).stdout.strip())
for line in open("SOURCES.sha256"):
    h, f = line.split()
    real = hashlib.sha256(open(f, "rb").read()).hexdigest()
    if real != h:
        say("SOURCE HASH MISMATCH", f); sys.exit(1)
say("sources verified, commit", open("COMMIT").read().strip())

os.makedirs("PeriodicNative", exist_ok=True)
for k in range(START, START + COUNT):
    with open("PeriodicNative/P%dB%d.lean" % (P, k), "w") as fh:
        fh.write("import PeriodicWordFast\n\nnamespace LangtonsAnt\n\n"
                 "theorem fastScan_%d_%d : fastScan %d %d (%d * %d) = true := by native_decide\n\n"
                 "end LangtonsAnt\n" % (P, k, P, W, W, k))

r = subprocess.run(["lake", "build", "PeriodicFastLib"], capture_output=True, text=True)
say("core build rc", r.returncode, r.stdout[-1500:], r.stderr[-1500:])
if r.returncode != 0:
    sys.exit(1)

os.makedirs(os.path.join(OUT, "blocks"), exist_ok=True)
done, failed = [], []
BATCH = 8
ks = list(range(START, START + COUNT))
per_batch = None
for i in range(0, len(ks), BATCH):
    batch = ks[i:i + BATCH]
    left = LIMIT - (time.time() - T0)
    need = (per_batch or 1800) * 1.3
    if left < need:
        say("stopping for time; left", int(left), "need", int(need)); break
    t = time.time()
    r = subprocess.run(["lake", "build"] + ["+PeriodicNative.P%dB%d" % (P, k) for k in batch],
                       capture_output=True, text=True)
    dt = time.time() - t
    per_batch = dt if per_batch is None else max(per_batch, dt)
    for k in batch:
        base = ".lake/build/lib/lean/PeriodicNative/P%dB%d" % (P, k)
        if os.path.exists(base + ".olean"):
            for ext in (".olean", ".ilean"):
                if os.path.exists(base + ext):
                    shutil.copy(base + ext, os.path.join(OUT, "blocks"))
            done.append(k)
        else:
            failed.append(k)
    say("batch", batch[0], "-", batch[-1], "rc", r.returncode, "%.0fs" % dt,
        "done", len(done), "failed", len(failed))
    if r.returncode != 0:
        say(r.stdout[-3000:], r.stderr[-3000:])

with open(os.path.join(OUT, "summary.txt"), "w") as fh:
    fh.write("P %d start %d count %d\ndone %s\nfailed %s\n" % (P, START, COUNT, done, failed))
say("finished: done", len(done), "failed", len(failed), "of", COUNT)
'''

def main():
    outdir, slug, P, start, count = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5])
    os.makedirs(outdir, exist_ok=True)
    code = TEMPLATE.replace("__P__", str(P)).replace("__START__", str(start)).replace("__COUNT__", str(count))
    open(os.path.join(outdir, "job.py"), "w", encoding="utf-8", newline="\n").write(code)
    meta = {"id": "aether254/" + slug, "title": slug, "code_file": "job.py", "language": "python",
            "kernel_type": "script", "is_private": True, "enable_gpu": False, "enable_internet": False,
            "dataset_sources": ["aether254/lean-ant-bundle"], "competition_sources": [], "kernel_sources": []}
    json.dump(meta, open(os.path.join(outdir, "kernel-metadata.json"), "w"), indent=1)

if __name__ == "__main__":
    main()
