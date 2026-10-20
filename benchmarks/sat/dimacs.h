// DIMACS CNF reader: the clause list flattened as [len, lits...]*, each
// literal x encoded 2(|x|-1) + (x < 0).
#pragma once
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <vector>

inline bool read_dimacs(const char *path, uint64_t &nvars,
                        std::vector<uint64_t> &flat) {
  FILE *f = std::fopen(path, "r");
  if (!f) return false;
  int c;
  long nv = 0, nc = 0;
  std::vector<uint64_t> cl;
  while ((c = std::fgetc(f)) != EOF) {
    if (c == 'c' || c == 'p') {
      if (c == 'p' && std::fscanf(f, " cnf %ld %ld", &nv, &nc) != 2) return false;
      while (c != '\n' && c != EOF) c = std::fgetc(f);
      continue;
    }
    if (c == '-' || (c >= '0' && c <= '9')) {
      std::ungetc(c, f);
      long x;
      if (std::fscanf(f, "%ld", &x) != 1) return false;
      if (x == 0) {
        flat.push_back(cl.size());
        flat.insert(flat.end(), cl.begin(), cl.end());
        cl.clear();
      } else {
        cl.push_back(2 * (uint64_t)(std::labs(x) - 1) + (x < 0));
      }
    }
  }
  std::fclose(f);
  nvars = (uint64_t)nv;
  return true;
}
