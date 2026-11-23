"""Extract fully-qualified names of PUBLIC theorems from a list of Lean modules.

Tracks nested `namespace` / `section` / `end` frames so that names declared inside
nested namespaces (e.g. `namespace Excursion`) get the correct full name.
Private theorems are skipped.
"""
import re
import sys
import os

ROOT = "D:/langtonsant"

MODULES = [
    # top-level files (D:/langtonsant/<Name>.lean)
    ("", "MixedWakeDefect"),
    ("", "DirectionTableTranslation"),
    ("", "DiagonalRankZeroLane"),
    ("", "DiagonalWinding"),
    ("", "RootWord"),
    ("", "WidthLemmas"),
    ("", "DiagonalReturnOrder"),
    ("", "WidthCutSum"),
    ("", "DiagonalSegments"),
    ("", "DiagonalTablePeriod"),
    ("", "RootTail"),
    ("", "WidthDefects"),
    ("", "BlackCountBound"),
    ("", "BlackCountBound2"),
    ("", "DirectionalBudget"),
    # PersistA subdirectory
    ("PersistA", "TimingCircuit"),
    ("PersistA", "TranslationShift"),
    ("PersistA", "GatePath"),
    ("PersistA", "TwoLaneCycle"),
    ("PersistA", "FirstVisitMap"),
    ("PersistA", "FiniteOrbitCycle"),
    ("PersistA", "FirstVisitCycle"),
    ("PersistA", "TwoGateDecomposition"),
    ("PersistA", "SharedBoundary"),
    ("PersistA", "GateRebase"),
]

# module name used in `import` (module names follow file paths from the project root)
def module_name(sub, name):
    return f"{sub}.{name}" if sub else name


IDENT = r"[A-Za-z_\u00a1-\uffff][A-Za-z0-9_'!?\u00a1-\uffff.]*"

ns_re = re.compile(r"^\s*namespace\s+(" + IDENT + r")\s*$")
sec_re = re.compile(r"^\s*(?:noncomputable\s+)?section\b")
end_re = re.compile(r"^\s*end(?:\s+(" + IDENT + r"))?\s*$")
thm_re = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)*"
    r"(private\s+|protected\s+|noncomputable\s+|partial\s+|unsafe\s+)*"
    r"(?:theorem|lemma)\s+(" + IDENT + r")"
)


def strip_comments(lines):
    """Remove -- line comments and nested /- -/ block comments (keep line count)."""
    out = []
    depth = 0
    for line in lines:
        res = []
        i = 0
        n = len(line)
        while i < n:
            if depth > 0:
                if line.startswith("/-", i):
                    depth += 1
                    i += 2
                elif line.startswith("-/", i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
            else:
                if line.startswith("/-", i):
                    depth += 1
                    i += 2
                elif line.startswith("--", i):
                    break
                else:
                    res.append(line[i])
                    i += 1
        out.append("".join(res))
    return out


def extract(path):
    with open(path, encoding="utf-8") as f:
        raw = f.read().splitlines()
    lines = strip_comments(raw)

    stack = []  # list of (kind, name)
    theorems = []  # (full_name, line_no, is_private)

    for idx, line in enumerate(lines, 1):
        m = end_re.match(line)
        if m:
            if stack:
                stack.pop()
            continue
        m = sec_re.match(line)
        if m:
            stack.append(("sec", None))
            continue
        m = ns_re.match(line)
        if m:
            stack.append(("ns", m.group(1)))
            continue
        m = thm_re.match(line)
        if m:
            mods = m.group(1) or ""
            name = m.group(2)
            prefix = [nm for kind, nm in stack if kind == "ns"]
            prefix = [p for p in prefix if p is not None]
            full = ".".join(prefix + [name])
            theorems.append((full, idx, "private" in mods))

    return theorems


def main():
    all_names = []
    for sub, name in MODULES:
        path = os.path.join(ROOT, sub, name + ".lean")
        thms = extract(path)
        pub = [(f, l) for f, l, p in thms if not p]
        priv = [f for f, l, p in thms if p]
        print(f"# {path}: {len(pub)} public, {len(priv)} private", file=sys.stderr)
        for f, l in pub:
            all_names.append(f)
    for n in all_names:
        print(n)


if __name__ == "__main__":
    main()
