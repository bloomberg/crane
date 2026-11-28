"""Summarize results.csv: per-instance times and the slowdown of the OCaml
build relative to Crane C++, with its geometric mean; checks that every
build agrees on the answer and the conflict count."""
import csv, math, sys
from collections import defaultdict

rows = list(csv.DictReader(open(sys.argv[1] if len(sys.argv) > 1 else "results.csv")))
by = defaultdict(dict)
for r in rows:
    by[r["instance"]][r["solver"]] = r
all_solvers = ["solver_cpp", "solver_ml"]
label = {"solver_cpp": "Crane C++", "solver_ml": "OCaml"}
# Only the builds results.csv has (run.sh's SOLVERS may select some).
solvers = [s for s in all_solvers if all(s in d for d in by.values())]
print("| instance | result | conflicts | " + " | ".join(label[s] for s in solvers) + " |")
print("|---" * (3 + len(solvers)) + "|")
ratios = defaultdict(list)
for inst in sorted(by):
    d = by[inst]
    assert len({(d[s]["result"], d[s]["conflicts"]) for s in solvers}) == 1, inst
    base = float(d[solvers[0]]["median_s"])
    cells = []
    for s in solvers:
        t = float(d[s]["median_s"])
        cells.append(f"{t:.3f}s" if s == solvers[0] else f"{t:.3f}s ({t / base:.2f}x)")
        if s != solvers[0]:
            ratios[s].append(t / base)
    print(f"| {inst} | {d[solvers[0]]['result']} | {d[solvers[0]]['conflicts']} | " + " | ".join(cells) + " |")
print()
for s in solvers[1:]:
    g = math.exp(sum(map(math.log, ratios[s])) / len(ratios[s]))
    print(f"geomean slowdown vs {label[solvers[0]]}, {label[s]}: {g:.2f}x (min {min(ratios[s]):.2f}x, max {max(ratios[s]):.2f}x)")
