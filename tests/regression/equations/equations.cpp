#include "equations.h"

bool PeanoNat::even(uint64_t n) {
  if (n <= 0) {
    return true;
  } else {
    uint64_t n0 = n - 1;
    if (n0 <= 0) {
      return false;
    } else {
      uint64_t n_ = n0 - 1;
      return PeanoNat::even(n_);
    }
  }
}

uint64_t PeanoNat::div2(uint64_t n) {
  if (n <= 0) {
    return UINT64_C(0);
  } else {
    uint64_t n0 = n - 1;
    if (n0 <= 0) {
      return UINT64_C(0);
    } else {
      uint64_t n_ = n0 - 1;
      return (PeanoNat::div2(n_) + 1);
    }
  }
}

uint64_t Equations::gcd(const std::pair<uint64_t, uint64_t> &x) {
  return gcd_functional(
      x, [](const std::pair<uint64_t, uint64_t> &y) { return gcd(y); });
}

uint64_t Equations::gcd_unfold_clause_3(uint64_t n, uint64_t n0, bool refine) {
  if (refine) {
    return gcd(std::make_pair(
        (n + 1),
        ((((n0 + 1) - (n + 1)) > (n0 + 1) ? 0 : ((n0 + 1) - (n + 1))))));
  } else {
    return gcd(std::make_pair(
        ((((n + 1) - (n0 + 1)) > (n + 1) ? 0 : ((n + 1) - (n0 + 1)))),
        (n0 + 1)));
  }
}

uint64_t Equations::gcd_unfold(std::pair<uint64_t, uint64_t> p) {
  uint64_t n = std::move(p.first);
  uint64_t n0 = std::move(p.second);
  if (n <= 0) {
    return n0;
  } else {
    uint64_t n1 = n - 1;
    if (n0 <= 0) {
      return (n1 + 1);
    } else {
      uint64_t n2 = n0 - 1;
      return gcd_unfold_clause_3(n1, n2, (n1 + 1) < (n2 + 1));
    }
  }
}

Equations::gcd_graph
Equations::gcd_graph_correct(std::pair<uint64_t, uint64_t> x) {
  uint64_t n = std::move(x.first);
  uint64_t n0 = std::move(x.second);
  if (n <= 0) {
    return gcd_graph::gcd_graph_equation_1(n0);
  } else {
    uint64_t n1 = n - 1;
    if (n0 <= 0) {
      return gcd_graph::gcd_graph_equation_2(n1);
    } else {
      uint64_t n2 = n0 - 1;
      return gcd_graph::gcd_graph_refinement_3(n1, n2, [&]() {
        bool refine = (n1 + 1) < (n2 + 1);
        if (refine) {
          return gcd_clause_3_graph::gcd_clause_3_graph_equation_1(
              n1, n2, [&]() {
                std::pair<uint64_t, uint64_t> y =
                    std::make_pair((n1 + 1), ((((n2 + 1) - (n1 + 1)) > (n2 + 1)
                                                   ? 0
                                                   : ((n2 + 1) - (n1 + 1)))));
                return gcd_graph_correct(std::move(y));
              }());
        } else {
          return gcd_clause_3_graph::gcd_clause_3_graph_equation_2(
              n1, n2, [&]() {
                std::pair<uint64_t, uint64_t> y =
                    std::make_pair(((((n1 + 1) - (n2 + 1)) > (n1 + 1)
                                         ? 0
                                         : ((n1 + 1) - (n2 + 1)))),
                                   (n2 + 1));
                return gcd_graph_correct(std::move(y));
              }());
        }
      }());
    }
  }
}

uint64_t Equations::collatz_steps(uint64_t x) {
  return collatz_steps_functional(x,
                                  [](uint64_t y) { return collatz_steps(y); });
}

uint64_t Equations::collatz_steps_unfold_clause_3(uint64_t n, bool refine) {
  if (refine) {
    return (collatz_steps(PeanoNat::div2(n)) + 1);
  } else {
    return (collatz_steps(((UINT64_C(3) * n) + UINT64_C(1))) + 1);
  }
}

uint64_t Equations::collatz_steps_unfold(uint64_t n) {
  if (n <= 0) {
    return UINT64_C(0);
  } else {
    uint64_t n0 = n - 1;
    if (n0 <= 0) {
      return UINT64_C(0);
    } else {
      uint64_t n1 = n0 - 1;
      return collatz_steps_unfold_clause_3(n1, PeanoNat::even(((n1 + 1) + 1)));
    }
  }
}

Equations::collatz_steps_graph
Equations::collatz_steps_graph_correct(uint64_t x) {
  if (x <= 0) {
    return collatz_steps_graph::collatz_steps_graph_equation_1();
  } else {
    uint64_t n = x - 1;
    if (n <= 0) {
      return collatz_steps_graph::collatz_steps_graph_equation_2();
    } else {
      uint64_t n0 = n - 1;
      return collatz_steps_graph::collatz_steps_graph_refinement_3(n0, [&]() {
        bool refine = PeanoNat::even(((n0 + 1) + 1));
        if (refine) {
          return collatz_steps_clause_3_graph::
              collatz_steps_clause_3_graph_equation_1(n0, [&]() {
                uint64_t y = PeanoNat::div2(n0);
                return collatz_steps_graph_correct(y);
              }());
        } else {
          return collatz_steps_clause_3_graph::
              collatz_steps_clause_3_graph_equation_2(n0, [&]() {
                uint64_t y = ((UINT64_C(3) * n0) + UINT64_C(1));
                return collatz_steps_graph_correct(y);
              }());
        }
      }());
    }
  }
}
