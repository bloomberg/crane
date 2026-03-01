#include <algorithm>
#include <any>
#include <cassert>
#include <equations.h>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

bool Nat::leb(const unsigned int n, const unsigned int m) {
  if (n <= 0) {
    return true;
  } else {
    unsigned int n_ = n - 1;
    if (m <= 0) {
      return false;
    } else {
      unsigned int m_ = m - 1;
      return leb(n_, m_);
    }
  }
}

bool Nat::ltb(const unsigned int n, const unsigned int m) {
  return leb((std::move(n) + 1), m);
}

bool Nat::even(const unsigned int n) {
  if (n <= 0) {
    return true;
  } else {
    unsigned int n0 = n - 1;
    if (n0 <= 0) {
      return false;
    } else {
      unsigned int n_ = n0 - 1;
      return even(n_);
    }
  }
}

unsigned int Nat::div2(const unsigned int n) {
  if (n <= 0) {
    return 0;
  } else {
    unsigned int n0 = n - 1;
    if (n0 <= 0) {
      return 0;
    } else {
      unsigned int n_ = n0 - 1;
      return (div2(n_) + 1);
    }
  }
}

unsigned int Equations::collatz_steps(const unsigned int _x0) {
  return [](const unsigned int _x0) {
    return Subterm::FixWf(collatz_steps_functional, _x0);
  }(_x0);
}

unsigned int Equations::collatz_steps_unfold_clause_3(const unsigned int n,
                                                      const bool refine) {
  if (refine) {
    return (collatz_steps(Nat::div2(std::move(n))) + 1);
  } else {
    return (collatz_steps((((((0 + 1) + 1) + 1) * std::move(n)) + (0 + 1))) +
            1);
  }
}

unsigned int Equations::collatz_steps_unfold(const unsigned int n) {
  if (n <= 0) {
    return 0;
  } else {
    unsigned int n0 = n - 1;
    if (n0 <= 0) {
      return 0;
    } else {
      unsigned int n1 = n0 - 1;
      return collatz_steps_unfold_clause_3(n1, Nat::even(((n1 + 1) + 1)));
    }
  }
}

std::shared_ptr<Equations::collatz_steps_graph>
Equations::collatz_steps_graph_correct(const unsigned int n) {
  return Subterm::FixWf(
      [](unsigned int x,
         std::function<std::shared_ptr<Equations::collatz_steps_graph>(
             unsigned int)>
             h) {
        if (x <= 0) {
          return collatz_steps_graph::ctor::collatz_steps_graph_equation_1_();
        } else {
          unsigned int n0 = x - 1;
          if (n0 <= 0) {
            return collatz_steps_graph::ctor::collatz_steps_graph_equation_2_();
          } else {
            unsigned int n1 = n0 - 1;
            return collatz_steps_graph::ctor::collatz_steps_graph_refinement_3_(
                n1, [&](void) {
                  bool refine = Nat::even(((n1 + 1) + 1));
                  if (refine) {
                    return collatz_steps_clause_3_graph::ctor::
                        collatz_steps_clause_3_graph_equation_1_(
                            n1, h(Nat::div2(n1)));
                  } else {
                    return collatz_steps_clause_3_graph::ctor::
                        collatz_steps_clause_3_graph_equation_2_(
                            n1, h((((((0 + 1) + 1) + 1) * n1) + (0 + 1))));
                  }
                }());
          }
        }
      },
      n);
}

unsigned int Equations::gcd(const std::pair<unsigned int, unsigned int> _x0) {
  return [](const std::pair<unsigned int, unsigned int> _x0) {
    return Subterm::FixWf(gcd_functional, _x0);
  }(_x0);
}

unsigned int Equations::gcd_unfold_clause_3(const unsigned int n,
                                            const unsigned int n0,
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

unsigned int
Equations::gcd_unfold(const std::pair<unsigned int, unsigned int> p) {
  unsigned int n = p.first;
  unsigned int n0 = p.second;
  if (n <= 0) {
    return 0;
  } else {
    unsigned int n1 = n - 1;
    if (n0 <= 0) {
      return 0;
    } else {
      unsigned int n2 = n0 - 1;
      return gcd_unfold_clause_3(n1, n2, Nat::ltb((n1 + 1), (n2 + 1)));
    }
  }
}

std::shared_ptr<Equations::gcd_graph>
Equations::gcd_graph_correct(const std::pair<unsigned int, unsigned int> p) {
  return Subterm::FixWf(
      [](std::pair<unsigned int, unsigned int> x,
         std::function<std::shared_ptr<Equations::gcd_graph>(
             std::pair<unsigned int, unsigned int>)>
             h) {
        unsigned int n = x.first;
        unsigned int n0 = x.second;
        if (n <= 0) {
          return gcd_graph::ctor::gcd_graph_equation_1_(n0);
        } else {
          unsigned int n1 = n - 1;
          if (n0 <= 0) {
            return gcd_graph::ctor::gcd_graph_equation_2_(n1);
          } else {
            unsigned int n2 = n0 - 1;
            return gcd_graph::ctor::gcd_graph_refinement_3_(n1, n2, [&](void) {
              bool refine = Nat::ltb((n1 + 1), (n2 + 1));
              if (refine) {
                return gcd_clause_3_graph::ctor::gcd_clause_3_graph_equation_1_(
                    n1, n2,
                    h(std::make_pair((n1 + 1),
                                     ((((n2 + 1) - (n1 + 1)) > (n2 + 1)
                                           ? 0
                                           : ((n2 + 1) - (n1 + 1)))))));
              } else {
                return gcd_clause_3_graph::ctor::gcd_clause_3_graph_equation_2_(
                    n1, n2,
                    h(std::make_pair(((((n1 + 1) - (n2 + 1)) > (n1 + 1)
                                           ? 0
                                           : ((n1 + 1) - (n2 + 1)))),
                                     (n2 + 1))));
              }
            }());
          }
        }
      },
      p);
}
