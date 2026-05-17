#include "fix_state_threading.h"

std::pair<List<uint64_t>, uint64_t>
FixStateThreading::reverse_count(const List<uint64_t> &l, List<uint64_t> acc) {
  if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
    return std::make_pair(std::move(acc), UINT64_C(0));
  } else {
    const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
    auto _cs = reverse_count(*a1, List<uint64_t>::cons(a0, std::move(acc)));
    const List<uint64_t> &acc_ = _cs.first;
    const uint64_t &n = _cs.second;
    return std::make_pair(std::move(_cs.first), (n + UINT64_C(1)));
  }
}

std::pair<List<uint64_t>, List<uint64_t>> FixStateThreading::collect_odds_evens(
    const List<uint64_t> &l, List<uint64_t> odds, List<uint64_t> evens) {
  if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
    return std::make_pair(std::move(odds), std::move(evens));
  } else {
    const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
    if (Nat::even(a0)) {
      return collect_odds_evens(*a1, std::move(odds),
                                List<uint64_t>::cons(a0, std::move(evens)));
    } else {
      return collect_odds_evens(*a1, List<uint64_t>::cons(a0, std::move(odds)),
                                std::move(evens));
    }
  }
}

std::pair<uint64_t, uint64_t>
FixStateThreading::sum_with_acc(const List<uint64_t> &l, uint64_t acc) {
  if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
    return std::make_pair(std::move(acc), UINT64_C(0));
  } else {
    const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
    auto _cs = sum_with_acc(*a1, (std::move(acc) + a0));
    const uint64_t &acc_ = _cs.first;
    const uint64_t &s = _cs.second;
    return std::make_pair(std::move(_cs.first), (s + UINT64_C(1)));
  }
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
