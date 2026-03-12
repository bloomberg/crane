#include <mutual_recursion.h>

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

bool MutualRecursion::even(const unsigned int n) {
  if (n <= 0) {
    return true;
  } else {
    unsigned int n_ = n - 1;
    return odd(n_);
  }
}

bool MutualRecursion::odd(const unsigned int n) {
  if (n <= 0) {
    return false;
  } else {
    unsigned int n_ = n - 1;
    return even(n_);
  }
}

unsigned int MutualRecursion::sum_even_indices(const unsigned int n,
                                               const unsigned int acc) {
  if (n <= 0) {
    return std::move(acc);
  } else {
    unsigned int n_ = n - 1;
    return sum_odd_indices(std::move(n_), acc);
  }
}

unsigned int MutualRecursion::sum_odd_indices(const unsigned int n,
                                              const unsigned int acc) {
  if (n <= 0) {
    return std::move(acc);
  } else {
    unsigned int n_ = n - 1;
    return sum_even_indices(std::move(n_), (acc + n));
  }
}

unsigned int MutualRecursion::process_a(const unsigned int n,
                                        const unsigned int m) {
  if (n <= 0) {
    return std::move(m);
  } else {
    unsigned int n_ = n - 1;
    return (process_b(std::move(n_), m) + n);
  }
}

unsigned int MutualRecursion::process_b(const unsigned int n,
                                        const unsigned int m) {
  if (n <= 0) {
    return std::move(m);
  } else {
    unsigned int n_ = n - 1;
    return (process_a(std::move(n_), m) + m);
  }
}

unsigned int
MutualRecursion::eval_expr(const std::shared_ptr<MutualRecursion::expr> &e) {
  return std::visit(
      Overloaded{
          [](const typename MutualRecursion::expr::Val _args) -> unsigned int {
            unsigned int n = _args._a0;
            return std::move(n);
          },
          [](const typename MutualRecursion::expr::BinOp _args)
              -> unsigned int {
            unsigned int op = _args._a0;
            std::shared_ptr<MutualRecursion::expr> l = _args._a1;
            std::shared_ptr<MutualRecursion::expr> r = _args._a2;
            if (op <= 0) {
              return (eval_expr(std::move(l)) + eval_expr(std::move(r)));
            } else {
              unsigned int _x = op - 1;
              return (eval_expr(std::move(l)) * eval_expr(std::move(r)));
            }
          },
          [](const typename MutualRecursion::expr::UnOp _args) -> unsigned int {
            unsigned int op = _args._a0;
            std::shared_ptr<MutualRecursion::expr> e_ = _args._a1;
            if (op <= 0) {
              return eval_expr(std::move(e_));
            } else {
              unsigned int _x = op - 1;
              return 0u;
            }
          }},
      e->v());
}

unsigned int MutualRecursion::f1(const unsigned int n) {
  if (n <= 0) {
    return 0u;
  } else {
    unsigned int n_ = n - 1;
    return (1u + f2(n_));
  }
}

unsigned int MutualRecursion::f2(const unsigned int n) {
  if (n <= 0) {
    return 0u;
  } else {
    unsigned int n_ = n - 1;
    return (2u + f3(n_));
  }
}

unsigned int MutualRecursion::f3(const unsigned int n) {
  if (n <= 0) {
    return 0u;
  } else {
    unsigned int n_ = n - 1;
    return (3u + f1(n_));
  }
}
