#!/usr/bin/env python3
"""
Checks the portability rule of `MPN32` and of the shared `MPN`: they must build wherever Lean does,
with nothing but Lean and its runtime, which is the only reason for 32-bit limbs.

* No `@[extern]`, `extern c inline` or `implemented_by` in `MPN.lean`, `MPN32.lean`,
  `MPN32Base.lean`, `MPN/` or `MPN32/` (the C of lean4-scalar-arrays below them is checked separately).
* The imports of `MPN32`, `MPN32Base` and `MPN`, transitively, reach no `MPN64` module (`MPN.Default`, the
  library `MPNDefault`, is outside the rule).
* Every runtime function that lean4-scalar-arrays names in an `extern` is declared in the
  toolchain's `lean.h`, and its inline C templates use no compiler extensions.

Run from the root of the package after `lake build` (which fetches the dependency); exits 1 with
the offending lines otherwise.
"""

import os
import re
import sys

ROOTS = ["MPN32", "MPN32Base", "MPN"]
EXEMPT = {"MPN.Default"}
FORBIDDEN = re.compile(r"@\[[^\]]*\b(extern|implemented_by)\b|extern\s+c\s+inline")
SA = ".lake/packages/lean4-scalar-arrays/ScalarArray"
EXTENSIONS = re.compile(r"__\w+|\(\{|\btypeof\b|\basm\b|__attribute__")

errors = []


def lean_files(path):
    for d, _, fs in os.walk(path):
        for f in fs:
            if f.endswith(".lean"):
                yield os.path.join(d, f)


def strip_comments(text):
    text = re.sub(r"/-.*?-/", lambda m: "\n" * m.group(0).count("\n"), text, flags=re.S)
    return re.sub(r"--[^\n]*", "", text)


# No foreign code in the portable sources.
for f in ["MPN.lean", "MPN32.lean", "MPN32Base.lean", *lean_files("MPN"), *lean_files("MPN32")]:
    if f.replace(os.sep, "/").removesuffix(".lean").replace("/", ".") in EXEMPT:
        continue
    for i, line in enumerate(strip_comments(open(f, encoding="utf-8").read()).splitlines(), 1):
        if FORBIDDEN.search(line):
            errors.append(f"{f}:{i}: foreign code: {line.strip()}")

# No path from the portable libraries to `MPN64`.
IMPORT = re.compile(r"^\s*(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?([\w.]+)", re.M)
parents = {}
todo = list(ROOTS)
seen = set()
while todo:
    m = todo.pop()
    if m in seen or m in EXEMPT:
        continue
    seen.add(m)
    path = m.replace(".", "/") + ".lean"
    if not os.path.exists(path):
        continue
    for dep in IMPORT.findall(strip_comments(open(path, encoding="utf-8").read())):
        parents.setdefault(dep, m)
        todo.append(dep)
for m in sorted(seen):
    if m == "MPN64" or m.startswith("MPN64."):
        chain = [m]
        while chain[-1] in parents and chain[-1] not in ROOTS:
            chain.append(parents[chain[-1]])
        errors.append("imports MPN64: " + " <- ".join(chain))

# The C of lean4-scalar-arrays: the runtime's own functions, in standard C.
if os.path.isdir(SA):
    lean_h = None
    for base in [os.environ.get("ELAN_HOME", os.path.expanduser("~/.elan")) + "/toolchains"]:
        tc = open("lean-toolchain").read().strip().replace("/", "--").replace(":", "---")
        cand = os.path.join(base, tc, "include", "lean", "lean.h")
        if os.path.exists(cand):
            lean_h = open(cand, encoding="utf-8").read()
    for f in lean_files(SA):
        text = strip_comments(open(f, encoding="utf-8").read())
        for name in re.findall(r'extern\s+"(\w+)"', text):
            if lean_h is not None and not re.search(r"\b" + name + r"\b", lean_h):
                errors.append(f"{f}: extern {name} is not in lean.h")
        for tmpl in re.findall(r'extern\s+c\s+inline\s+"((?:[^"\\]|\\.)*)"', text):
            if EXTENSIONS.search(tmpl):
                errors.append(f"{f}: inline C with a compiler extension: {tmpl}")
    if lean_h is None:
        print("note: lean.h of the toolchain not found; the extern names were not checked")
else:
    print(f"note: {SA} not found; run `lake build` first to check the dependency")

if errors:
    print("\n".join(errors))
    sys.exit(1)
print(f"portable: {len(seen)} modules of MPN32 and MPN, no foreign code, no MPN64")
