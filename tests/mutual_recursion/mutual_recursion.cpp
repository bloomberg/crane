#include "mutual_recursion.h"

bool MutualRecursion::even(uint64_t n) {
  if (n <= 0) {
    return true;
  } else {
    uint64_t n_ = n - 1;
    return odd(n_);
  }
}

bool MutualRecursion::odd(uint64_t n) {
  if (n <= 0) {
    return false;
  } else {
    uint64_t n_ = n - 1;
    return even(n_);
  }
}

uint64_t MutualRecursion::sum_even_indices(uint64_t n, uint64_t acc) {
  if (n <= 0) {
    return acc;
  } else {
    uint64_t n_ = n - 1;
    return sum_odd_indices(n_, acc);
  }
}

uint64_t MutualRecursion::sum_odd_indices(uint64_t n, uint64_t acc) {
  if (n <= 0) {
    return acc;
  } else {
    uint64_t n_ = n - 1;
    return sum_even_indices(n_, (acc + n));
  }
}

uint64_t MutualRecursion::process_a(uint64_t n, uint64_t m) {
  if (n <= 0) {
    return m;
  } else {
    uint64_t n_ = n - 1;
    return (process_b(n_, m) + n);
  }
}

uint64_t MutualRecursion::process_b(uint64_t n, uint64_t m) {
  if (n <= 0) {
    return m;
  } else {
    uint64_t n_ = n - 1;
    return (process_a(n_, m) + m);
  }
}

uint64_t MutualRecursion::eval_expr(const MutualRecursion::expr &e) {
  if (std::holds_alternative<typename MutualRecursion::expr::Val>(e.v())) {
    const auto &[a0] = std::get<typename MutualRecursion::expr::Val>(e.v());
    return a0;
  } else if (std::holds_alternative<typename MutualRecursion::expr::BinOp>(
                 e.v())) {
    const auto &[a0, a1, a2] =
        std::get<typename MutualRecursion::expr::BinOp>(e.v());
    if (a0 <= 0) {
      return (eval_expr(*a1) + eval_expr(*a2));
    } else {
      uint64_t _x = a0 - 1;
      return (eval_expr(*a1) * eval_expr(*a2));
    }
  } else {
    const auto &[a0, a1] =
        std::get<typename MutualRecursion::expr::UnOp>(e.v());
    if (a0 <= 0) {
      return eval_expr(*a1);
    } else {
      uint64_t _x = a0 - 1;
      return UINT64_C(0);
    }
  }
}

uint64_t MutualRecursion::f1(uint64_t n) {
  if (n <= 0) {
    return UINT64_C(0);
  } else {
    uint64_t n_ = n - 1;
    return (UINT64_C(1) + f2(n_));
  }
}

uint64_t MutualRecursion::f2(uint64_t n) {
  if (n <= 0) {
    return UINT64_C(0);
  } else {
    uint64_t n_ = n - 1;
    return (UINT64_C(2) + f3(n_));
  }
}

uint64_t MutualRecursion::f3(uint64_t n) {
  if (n <= 0) {
    return UINT64_C(0);
  } else {
    uint64_t n_ = n - 1;
    return (UINT64_C(3) + f1(n_));
  }
}
