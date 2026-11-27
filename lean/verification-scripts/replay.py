#!/usr/bin/env python3
"""Replay the project in source-dependency order with one Lean worker."""
import argparse
import os
import re
import subprocess
from graphlib import TopologicalSorter
from pathlib import Path

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--fresh", action="store_true",
                    help="recheck every project declaration, including previously built dependencies")
parser.add_argument("--historical", action="store_true",
                    help="also replay the historical closed degree-eight and degree-nine targets")
parser.add_argument("--memory", type=int, metavar="MB",
                    help="optional maximum memory for each Lean process")
args = parser.parse_args()
root = Path(__file__).resolve().parents[1]
os.chdir(root)
output = root / ".lake" / "build" / "lib" / "lean"
environment = dict(os.environ)
lean_path = subprocess.check_output(["lake", "env", "printenv", "LEAN_PATH"],
                                    text=True).strip()
environment["LEAN_PATH"] = str(output) + os.pathsep + lean_path
lean_executable = subprocess.check_output(["lake", "env", "which", "lean"],
                                          text=True).strip()
sources = {p.relative_to(root).with_suffix("").as_posix().replace("/", "."): p
           for p in root.rglob("*.lean")
           if not any(part.startswith(".") for part in p.relative_to(root).parts)}
graph = {}
def visit(name):
    if name in graph:
        return
    path = sources[name]
    imports = [dep for line in re.findall(r"^import\s+([^\n]+)", path.read_text(), re.M)
               for dep in line.split() if dep in sources]
    graph[name] = imports
    for dep in imports:
        visit(dep)
visit("WaringLinear")
if args.historical:
    for endpoint in ["Waring.ValidatedTarget8", "Waring.ValidatedTarget9", "HistoricalAudit"]:
        visit(endpoint)
if "Audit" in sources:
    visit("Audit")
if "DegreeDrop" in sources:
    visit("DegreeDrop")
order = tuple(TopologicalSorter(graph).static_order())
for i, name in enumerate(order, 1):
    source = sources[name]
    olean = output / source.relative_to(root).with_suffix(".olean")
    prerequisites = [source] + [output / sources[dep].relative_to(root).with_suffix(".olean")
                                for dep in graph[name]]
    if (not args.fresh and olean.exists()
            and all(p.stat().st_mtime <= olean.stat().st_mtime for p in prerequisites)):
        continue
    print(f"[{i}/{len(order)}] {name}", flush=True)
    olean.parent.mkdir(parents=True, exist_ok=True)
    options = ["-j1"]
    if args.memory is not None:
        options.extend(["-M", str(args.memory)])
    subprocess.run([lean_executable, *options, "-o", str(olean), str(source.relative_to(root))],
                   check=True, env=environment)
