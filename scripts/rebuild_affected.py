#!/usr/bin/env python3
"""Recompile, in dependency order, exactly the modules affected by a change set.

Law 5 forbids `lake build` (racing builds); this drives `lake env lean -o` one
module at a time over the topologically-sorted affected subgraph, so the olean
tree stays consistent without ever invoking lake's builder.

Usage: python3 scripts/rebuild_affected.py <changed.lean> [<changed.lean> ...]
       python3 scripts/rebuild_affected.py --list <changed.lean> ...   (dry run)
"""
import os, re, sys, subprocess, time

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
os.chdir(ROOT)

def mod_of(path):
    return path[:-5].replace("/", ".") if path.endswith(".lean") else path

def path_of(mod):
    return mod.replace(".", "/") + ".lean"

files = []
for base in ("Vsa", "."):
    for dirpath, _, names in os.walk(base):
        if ".lake" in dirpath or dirpath.startswith("./.lake"):
            continue
        for n in names:
            if n.endswith(".lean"):
                p = os.path.normpath(os.path.join(dirpath, n))
                if p.startswith("Vsa") or p in ("Vsa.lean", "VsaRun.lean"):
                    files.append(p)
files = sorted(set(files))
imports = {}
for f in files:
    with open(f, encoding="utf-8") as fh:
        head = []
        for line in fh:
            m = re.match(r"^import\s+([\w.]+)", line)
            if m:
                head.append(m.group(1))
            elif line.strip() and not line.startswith("--"):
                break
    imports[mod_of(f)] = [m for m in head if path_of(m) in files]

args = [a for a in sys.argv[1:] if not a.startswith("--")]
dry = "--list" in sys.argv
changed = {mod_of(os.path.normpath(a)) for a in args}

# reverse reachability: every module that transitively imports a changed one
rev = {}
for m, deps in imports.items():
    for d in deps:
        rev.setdefault(d, []).append(m)
affected, stack = set(changed), list(changed)
while stack:
    m = stack.pop()
    for u in rev.get(m, []):
        if u not in affected:
            affected.add(u); stack.append(u)

# topological order over the affected subgraph
order, seen = [], set()
def visit(m):
    if m in seen: return
    seen.add(m)
    for d in imports.get(m, []):
        if d in affected:
            visit(d)
    order.append(m)
for m in sorted(affected):
    visit(m)

print(f"{len(order)} affected modules")
if dry:
    for m in order: print("  ", m)
    sys.exit(0)

# ---- dependency-respecting parallel waves --------------------------------
import concurrent.futures, threading

JOBS = int(os.environ.get("REBUILD_JOBS", "8"))
deps = {m: {d for d in imports.get(m, []) if d in affected} for m in affected}
pending = dict(deps)
done, failed = set(), []
lock = threading.Lock()
total, count = len(order), 0

SKIP_FRESH = os.environ.get("REBUILD_SKIP_FRESH", "1") == "1"

def olean_of(m):
    return os.path.join(".lake/build/lib/lean", m.replace(".", "/") + ".olean")

def fresh(m):
    """Olean newer than its source AND than every affected dependency's olean.
    Compiling in dependency order makes this exact: a rebuilt dep gets a newer
    mtime, which forces every downstream module to rebuild."""
    if not SKIP_FRESH:
        return False
    o = olean_of(m)
    if not os.path.exists(o):
        return False
    t = os.path.getmtime(o)
    if t <= os.path.getmtime(path_of(m)):
        return False
    for d in deps[m]:
        od = olean_of(d)
        if not os.path.exists(od) or os.path.getmtime(od) >= t:
            return False
    return True

def build(m):
    if fresh(m):
        return m, True, "", 0.0
    src = path_of(m)
    olean = olean_of(m)
    os.makedirs(os.path.dirname(olean), exist_ok=True)
    t0 = time.time()
    r = subprocess.run(["lake", "env", "lean", "-o", olean, src],
                       capture_output=True, text=True)
    out = r.stdout + r.stderr
    ok = r.returncode == 0 and "error" not in out
    return m, ok, out, time.time() - t0

with concurrent.futures.ThreadPoolExecutor(max_workers=JOBS) as ex:
    inflight = {}
    while (pending or inflight) and not failed:
        ready = [m for m, d in pending.items() if not (d - done)]
        for m in ready:
            del pending[m]
            inflight[ex.submit(build, m)] = m
        if not inflight:
            break
        fin, _ = concurrent.futures.wait(inflight, return_when=concurrent.futures.FIRST_COMPLETED)
        for f in fin:
            m = inflight.pop(f)
            mm, ok, out, dt = f.result()
            with lock:
                count += 1
                if ok:
                    done.add(mm)
                    print(f"[{count}/{total}] {'skip' if dt == 0.0 else 'ok  '} {mm}  ({dt:.1f}s)", flush=True)
                else:
                    print(f"[{count}/{total}] FAIL {mm}  ({dt:.1f}s)", flush=True)
                    print(out[:6000], flush=True)
                    failed.append(mm)

if failed:
    print("BUILD FAILED:", failed)
    sys.exit(1)
if pending:
    print("BLOCKED (unbuilt deps):", sorted(pending)[:10])
    sys.exit(1)
print("ALL GREEN")
