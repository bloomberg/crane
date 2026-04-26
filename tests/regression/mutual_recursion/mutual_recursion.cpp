#include <mutual_recursion.h>

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) bool MutualRecursion::even(const unsigned int &n) {
  if (n <= 0) {
    return true;
  } else {
    unsigned int n_ = n - 1;
    return odd(n_);
  }
}

__attribute__((pure)) bool MutualRecursion::odd(const unsigned int &n) {
  if (n <= 0) {
    return false;
  } else {
    unsigned int n_ = n - 1;
    return even(n_);
  }
}

__attribute__((pure)) unsigned int
MutualRecursion::sum_even_indices(const unsigned int &n, unsigned int acc) {
  if (n <= 0) {
    return acc;
  } else {
    unsigned int n_ = n - 1;
    return sum_odd_indices(n_, acc);
  }
}

__attribute__((pure)) unsigned int
MutualRecursion::sum_odd_indices(const unsigned int &n, unsigned int acc) {
  if (n <= 0) {
    return acc;
  } else {
    unsigned int n_ = n - 1;
    return sum_even_indices(n_, (acc + n));
  }
}

__attribute__((pure)) unsigned int
MutualRecursion::process_a(const unsigned int &n, unsigned int m) {
  if (n <= 0) {
    return m;
  } else {
    unsigned int n_ = n - 1;
    return (process_b(n_, m) + n);
  }
}

__attribute__((pure)) unsigned int
MutualRecursion::process_b(const unsigned int &n, unsigned int m) {
  if (n <= 0) {
    return m;
  } else {
    unsigned int n_ = n - 1;
    return (process_a(n_, m) + m);
  }
}

__attribute__((pure)) unsigned int
MutualRecursion::eval_expr(const MutualRecursion::expr &e) {
  if (std::holds_alternative<typename MutualRecursion::expr::Val>(e.v())) {
    const auto &[d_a0] = std::get<typename MutualRecursion::expr::Val>(e.v());
    return d_a0;
  } else if (std::holds_alternative<typename MutualRecursion::expr::BinOp>(
                 e.v())) {
    const auto &[d_a0, d_a1, d_a2] =
        std::get<typename MutualRecursion::expr::BinOp>(e.v());
    if (d_a0 <= 0) {
      return (eval_expr(*(d_a1)) + eval_expr(*(d_a2)));
    } else {
      unsigned int _x = d_a0 - 1;
      return (eval_expr(*(d_a1)) * eval_expr(*(d_a2)));
    }
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename MutualRecursion::expr::UnOp>(e.v());
    if (d_a0 <= 0) {
      return eval_expr(*(d_a1));
    } else {
      unsigned int _x = d_a0 - 1;
      return 0u;
    }
  }
}

__attribute__((pure)) unsigned int MutualRecursion::f1(const unsigned int &n) {
  if (n <= 0) {
    return 0u;
  } else {
    unsigned int n_ = n - 1;
    return (1u + f2(n_));
  }
}

__attribute__((pure)) unsigned int MutualRecursion::f2(const unsigned int &n) {
  if (n <= 0) {
    return 0u;
  } else {
    unsigned int n_ = n - 1;
    return (2u + f3(n_));
  }
}

__attribute__((pure)) unsigned int MutualRecursion::f3(const unsigned int &n) {
  if (n <= 0) {
    return 0u;
  } else {
    unsigned int n_ = n - 1;
    return (3u + f1(n_));
  }
}
