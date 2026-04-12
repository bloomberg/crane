#include <equations.h>

#include <any>
#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) bool PeanoNat::even(const unsigned int n) {
  if (n <= 0) {
    return true;
  } else {
    unsigned int n0 = n - 1;
    if (n0 <= 0) {
      return false;
    } else {
      unsigned int n_ = n0 - 1;
      return PeanoNat::even(n_);
    }
  }
}

__attribute__((pure)) unsigned int PeanoNat::div2(const unsigned int n) {
  if (n <= 0) {
    return 0u;
  } else {
    unsigned int n0 = n - 1;
    if (n0 <= 0) {
      return 0u;
    } else {
      unsigned int n_ = n0 - 1;
      return (PeanoNat::div2(n_) + 1);
    }
  }
}

__attribute__((pure)) unsigned int
Equations::gcd(const std::pair<unsigned int, unsigned int> x) {
  return gcd_functional(
      x, [](std::pair<unsigned int, unsigned int> y) { return gcd(y); });
}

__attribute__((pure)) unsigned int
Equations::gcd_unfold_clause_3(const unsigned int n, const unsigned int n0,
                               const bool refine) {
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

__attribute__((pure)) unsigned int
Equations::gcd_unfold(const std::pair<unsigned int, unsigned int> p) {
  const unsigned int &n = p.first;
  const unsigned int &n0 = p.second;
  if (n <= 0) {
    return n0;
  } else {
    unsigned int n1 = n - 1;
    if (n0 <= 0) {
      return (n1 + 1);
    } else {
      unsigned int n2 = n0 - 1;
      return gcd_unfold_clause_3(n1, n2, (n1 + 1) < (n2 + 1));
    }
  }
}

std::shared_ptr<Equations::gcd_graph>
Equations::gcd_graph_correct(const std::pair<unsigned int, unsigned int> x) {
  const unsigned int &n = x.first;
  const unsigned int &n0 = x.second;
  if (n <= 0) {
    return gcd_graph::gcd_graph_equation_1(n0);
  } else {
    unsigned int n1 = n - 1;
    if (n0 <= 0) {
      return gcd_graph::gcd_graph_equation_2(n1);
    } else {
      unsigned int n2 = n0 - 1;
      return gcd_graph::gcd_graph_refinement_3(n1, n2, [&]() {
        bool refine = (n1 + 1) < (n2 + 1);
        if (refine) {
          return gcd_clause_3_graph::gcd_clause_3_graph_equation_1(
              n1, n2, [&]() {
                std::pair<unsigned int, unsigned int> y =
                    std::make_pair((n1 + 1), ((((n2 + 1) - (n1 + 1)) > (n2 + 1)
                                                   ? 0
                                                   : ((n2 + 1) - (n1 + 1)))));
                return gcd_graph_correct(y);
              }());
        } else {
          return gcd_clause_3_graph::gcd_clause_3_graph_equation_2(
              n1, n2, [&]() {
                std::pair<unsigned int, unsigned int> y =
                    std::make_pair(((((n1 + 1) - (n2 + 1)) > (n1 + 1)
                                         ? 0
                                         : ((n1 + 1) - (n2 + 1)))),
                                   (n2 + 1));
                return gcd_graph_correct(y);
              }());
        }
      }());
    }
  }
}

__attribute__((pure)) unsigned int
Equations::collatz_steps(const unsigned int x) {
  return collatz_steps_functional(
      x, [](unsigned int y) { return collatz_steps(y); });
}

__attribute__((pure)) unsigned int
Equations::collatz_steps_unfold_clause_3(const unsigned int n,
                                         const bool refine) {
  if (refine) {
    return (collatz_steps(PeanoNat::div2(n)) + 1);
  } else {
    return (collatz_steps(((3u * n) + 1u)) + 1);
  }
}

__attribute__((pure)) unsigned int
Equations::collatz_steps_unfold(const unsigned int n) {
  if (n <= 0) {
    return 0u;
  } else {
    unsigned int n0 = n - 1;
    if (n0 <= 0) {
      return 0u;
    } else {
      unsigned int n1 = n0 - 1;
      return collatz_steps_unfold_clause_3(n1, PeanoNat::even(((n1 + 1) + 1)));
    }
  }
}

std::shared_ptr<Equations::collatz_steps_graph>
Equations::collatz_steps_graph_correct(const unsigned int x) {
  if (x <= 0) {
    return collatz_steps_graph::collatz_steps_graph_equation_1();
  } else {
    unsigned int n = x - 1;
    if (n <= 0) {
      return collatz_steps_graph::collatz_steps_graph_equation_2();
    } else {
      unsigned int n0 = n - 1;
      return collatz_steps_graph::collatz_steps_graph_refinement_3(n0, [&]() {
        bool refine = PeanoNat::even(((n0 + 1) + 1));
        if (refine) {
          return collatz_steps_clause_3_graph::
              collatz_steps_clause_3_graph_equation_1(n0, [&]() {
                unsigned int y = PeanoNat::div2(n0);
                return collatz_steps_graph_correct(y);
              }());
        } else {
          return collatz_steps_clause_3_graph::
              collatz_steps_clause_3_graph_equation_2(n0, [&]() {
                unsigned int y = ((3u * n0) + 1u);
                return collatz_steps_graph_correct(y);
              }());
        }
      }());
    }
  }
}
