"""Summarize results.csv: per-instance times and speedup of Crane C++ over
each OCaml build, with geometric means; checks every build agrees on the
answer and the conflict count."""
import csv, math, sys
from collections import defaultdict

rows = list(csv.DictReader(open(sys.argv[1] if len(sys.argv) > 1 else "results.csv")))
by = defaultdict(dict)
for r in rows:
    by[r["instance"]][r["solver"]] = r
solvers = ["solver_cpp", "solver_direct_ml_fl", "solver_direct_ml", "solver_ml_fl", "solver_ml"]
label = {"solver_cpp": "Crane C++", "solver_direct_ml_fl": "OCaml erased (flambda)",
         "solver_direct_ml": "OCaml erased", "solver_ml_fl": "OCaml itree (flambda)",
         "solver_ml": "OCaml itree"}
print("| instance | result | conflicts | " + " | ".join(label[s] for s in solvers) + " |")
print("|---" * (3 + len(solvers)) + "|")
ratios = defaultdict(list)
for inst in sorted(by):
    d = by[inst]
    assert len({(d[s]["result"], d[s]["conflicts"]) for s in solvers}) == 1, inst
    base = float(d["solver_cpp"]["median_s"])
    cells = []
    for s in solvers:
        t = float(d[s]["median_s"])
        cells.append(f"{t:.3f}s" if s == "solver_cpp" else f"{t:.3f}s ({t / base:.0f}×)")
        if s != "solver_cpp":
            ratios[s].append(t / base)
    print(f"| {inst} | {d['solver_cpp']['result']} | {d['solver_cpp']['conflicts']} | " + " | ".join(cells) + " |")
print()
for s in solvers[1:]:
    g = math.exp(sum(map(math.log, ratios[s])) / len(ratios[s]))
    print(f"geomean slowdown vs Crane, {label[s]}: {g:.1f}× (min {min(ratios[s]):.1f}×, max {max(ratios[s]):.1f}×)")
