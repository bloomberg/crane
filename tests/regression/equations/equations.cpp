#include <equations.h>

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

__attribute__((pure)) bool PeanoNat::leb(const unsigned int n,
                                         const unsigned int m) {
  if (n <= 0) {
    return true;
  } else {
    unsigned int n_ = n - 1;
    if (m <= 0) {
      return false;
    } else {
      unsigned int m_ = m - 1;
      return PeanoNat::leb(n_, m_);
    }
  }
}

__attribute__((pure)) bool PeanoNat::ltb(const unsigned int n,
                                         const unsigned int m) {
  return PeanoNat::leb((std::move(n) + 1), m);
}

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
        (n + 1), ((((std::move(n0) + 1) - (n + 1)) > (std::move(n0) + 1)
                       ? 0
                       : ((std::move(n0) + 1) - (n + 1))))));
  } else {
    return gcd(
        std::make_pair(((((std::move(n) + 1) - (n0 + 1)) > (std::move(n) + 1)
                             ? 0
                             : ((std::move(n) + 1) - (n0 + 1)))),
                       (n0 + 1)));
  }
}

__attribute__((pure)) unsigned int
Equations::gcd_unfold(const std::pair<unsigned int, unsigned int> p) {
  unsigned int n = p.first;
  unsigned int n0 = p.second;
  if (n <= 0) {
    return n0;
  } else {
    unsigned int n1 = n - 1;
    if (n0 <= 0) {
      return (n1 + 1);
    } else {
      unsigned int n2 = n0 - 1;
      return gcd_unfold_clause_3(n1, n2, PeanoNat::ltb((n1 + 1), (n2 + 1)));
    }
  }
}

std::shared_ptr<Equations::gcd_graph>
Equations::gcd_graph_correct(const std::pair<unsigned int, unsigned int> x) {
  unsigned int n = x.first;
  unsigned int n0 = x.second;
  if (n <= 0) {
    return gcd_graph::ctor::Gcd_graph_equation_1_(n0);
  } else {
    unsigned int n1 = n - 1;
    if (n0 <= 0) {
      return gcd_graph::ctor::Gcd_graph_equation_2_(n1);
    } else {
      unsigned int n2 = n0 - 1;
      return gcd_graph::ctor::Gcd_graph_refinement_3_(n1, n2, [&](void) {
        bool refine = PeanoNat::ltb((n1 + 1), (n2 + 1));
        if (std::move(refine)) {
          return gcd_clause_3_graph::ctor::Gcd_clause_3_graph_equation_1_(
              n1, n2, [&](void) {
                std::pair<unsigned int, unsigned int> y =
                    std::make_pair((n1 + 1), ((((n2 + 1) - (n1 + 1)) > (n2 + 1)
                                                   ? 0
                                                   : ((n2 + 1) - (n1 + 1)))));
                return gcd_graph_correct(std::move(y));
              }());
        } else {
          return gcd_clause_3_graph::ctor::Gcd_clause_3_graph_equation_2_(
              n1, n2, [&](void) {
                std::pair<unsigned int, unsigned int> y =
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

__attribute__((pure)) unsigned int
Equations::collatz_steps(const unsigned int x) {
  return collatz_steps_functional(
      x, [](unsigned int y) { return collatz_steps(y); });
}

__attribute__((pure)) unsigned int
Equations::collatz_steps_unfold_clause_3(const unsigned int n,
                                         const bool refine) {
  if (refine) {
    return (collatz_steps(PeanoNat::div2(std::move(n))) + 1);
  } else {
    return (collatz_steps(((3u * std::move(n)) + 1u)) + 1);
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
    return collatz_steps_graph::ctor::Collatz_steps_graph_equation_1_();
  } else {
    unsigned int n = x - 1;
    if (n <= 0) {
      return collatz_steps_graph::ctor::Collatz_steps_graph_equation_2_();
    } else {
      unsigned int n0 = n - 1;
      return collatz_steps_graph::ctor::Collatz_steps_graph_refinement_3_(
          n0, [&](void) {
            bool refine = PeanoNat::even(((n0 + 1) + 1));
            if (std::move(refine)) {
              return collatz_steps_clause_3_graph::ctor::
                  Collatz_steps_clause_3_graph_equation_1_(n0, [&](void) {
                    unsigned int y = PeanoNat::div2(n0);
                    return collatz_steps_graph_correct(std::move(y));
                  }());
            } else {
              return collatz_steps_clause_3_graph::ctor::
                  Collatz_steps_clause_3_graph_equation_2_(n0, [&](void) {
                    unsigned int y = ((3u * n0) + 1u);
                    return collatz_steps_graph_correct(std::move(y));
                  }());
            }
          }());
    }
  }
}
