"""Benchmark instances: uniform random 3-SAT at a given clause/variable
ratio, and pigeonhole PHP(n+1, n) (always unsatisfiable)."""
import random, sys

def rand3(n, ratio, seed, out):
    rng = random.Random(seed)
    m = round(n * ratio)
    with open(out, "w") as f:
        f.write(f"p cnf {n} {m}\n")
        for _ in range(m):
            vs = rng.sample(range(1, n + 1), 3)
            f.write(" ".join(str(v if rng.random() < 0.5 else -v) for v in vs) + " 0\n")

def php(n, out):
    holes, pigeons = n, n + 1
    var = lambda p, h: p * holes + h + 1
    cls = [[var(p, h) for h in range(holes)] for p in range(pigeons)]
    for h in range(holes):
        for p in range(pigeons):
            for q in range(p + 1, pigeons):
                cls.append([-var(p, h), -var(q, h)])
    with open(out, "w") as f:
        f.write(f"p cnf {pigeons * holes} {len(cls)}\n")
        for c in cls:
            f.write(" ".join(map(str, c)) + " 0\n")

if __name__ == "__main__":
    kind = sys.argv[1]
    if kind == "rand3":
        rand3(int(sys.argv[2]), float(sys.argv[3]), int(sys.argv[4]), sys.argv[5])
    elif kind == "php":
        php(int(sys.argv[2]), sys.argv[3])
