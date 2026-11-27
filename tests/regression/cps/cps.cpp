#include "cps.h"

uint64_t CPS::fact_cps(uint64_t n, const crane::fn<uint64_t(uint64_t)> &k) {
  if (n <= 0) {
    return k(UINT64_C(1));
  } else {
    uint64_t n_ = n - 1;
    return fact_cps(n_, [=, k = k](uint64_t r) { return k(((n_ + 1)) * r); });
  }
}

uint64_t CPS::factorial(uint64_t n) {
  return fact_cps(n, [](uint64_t x) { return x; });
}

uint64_t CPS::fib_cps(uint64_t n, const crane::fn<uint64_t(uint64_t)> &k) {
  if (n <= 0) {
    return k(UINT64_C(0));
  } else {
    uint64_t n1 = n - 1;
    if (n1 <= 0) {
      return k(UINT64_C(1));
    } else {
      uint64_t n_ = n1 - 1;
      return fib_cps(n_, [=, k = k](uint64_t a) {
        return fib_cps(n1, [=, k = k](uint64_t b) { return k(a + b); });
      });
    }
  }
}

uint64_t CPS::fibonacci(uint64_t n) {
  return fib_cps(n, [](uint64_t x) { return x; });
}

uint64_t CPS::tree_sum_cps(const CPS::tree &t,
                           const crane::fn<uint64_t(uint64_t)> &k) {
  if (std::holds_alternative<typename CPS::tree::Leaf>(t.v())) {
    const auto &[a0] = std::get<typename CPS::tree::Leaf>(t.v());
    return k(a0);
  } else {
    const auto &[a0, a1] = std::get<typename CPS::tree::Node>(t.v());
    const CPS::tree &a0_value = *a0;
    const CPS::tree &a1_value = *a1;
    return tree_sum_cps(a0_value, [=, a1_value = a1_value, k = k](uint64_t sl) {
      return tree_sum_cps(a1_value,
                          [=, k = k](uint64_t sr) { return k(sl + sr); });
    });
  }
}

uint64_t CPS::tree_sum(const CPS::tree &t) {
  return tree_sum_cps(t, [](uint64_t x) { return x; });
}

uint64_t CPS::sum_cps(const List<uint64_t> &l,
                      const crane::fn<uint64_t(uint64_t)> &k) {
  if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
    return k(UINT64_C(0));
  } else {
    const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
    const List<uint64_t> &a1_value = *a1;
    return sum_cps(a1_value, [=, k = k](uint64_t r) { return k(a0 + r); });
  }
}

uint64_t CPS::list_sum(const List<uint64_t> &l) {
  return sum_cps(l, [](uint64_t x) { return x; });
}

uint64_t
CPS::partition_cps(crane::fn<bool(uint64_t)> p, const List<uint64_t> &l,
                   crane::fn<uint64_t(List<uint64_t>, List<uint64_t>)> k) {
  if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
    return k(List<uint64_t>::nil(), List<uint64_t>::nil());
  } else {
    const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
    const List<uint64_t> &a1_value = *a1;
    return partition_cps(p, a1_value,
                         [=, k = std::move(k)](const List<uint64_t> &yes,
                                               const List<uint64_t> &no)
                              -> uint64_t {
                           if (p(a0)) {
                             return k(List<uint64_t>::cons(a0, yes), no);
                           } else {
                             return k(yes, List<uint64_t>::cons(a0, no));
                           }
                         });
  }
}

uint64_t CPS::count_evens(const List<uint64_t> &l) {
  return partition_cps(
      Nat::even, l,
      [](const List<uint64_t> &yes, List<uint64_t>) { return yes.length(); });
}

bool Nat::even(uint64_t n) {
  if (n <= 0) {
    return true;
  } else {
    uint64_t n0 = n - 1;
    if (n0 <= 0) {
      return false;
    } else {
      uint64_t n_ = n0 - 1;
      return Nat::even(n_);
    }
  }
}
