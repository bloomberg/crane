#include "fix_state_threading.h"

std::pair<List<unsigned int>, unsigned int>
FixStateThreading::reverse_count(const List<unsigned int> &l,
                                 List<unsigned int> acc) {
  if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
    return std::make_pair(std::move(acc), 0u);
  } else {
    const auto &[a0, a1] = std::get<typename List<unsigned int>::Cons>(l.v());
    auto _cs = reverse_count(*a1, List<unsigned int>::cons(a0, std::move(acc)));
    const List<unsigned int> &acc_ = _cs.first;
    const unsigned int &n = _cs.second;
    return std::make_pair(std::move(_cs.first), (n + 1u));
  }
}

std::pair<List<unsigned int>, List<unsigned int>>
FixStateThreading::collect_odds_evens(const List<unsigned int> &l,
                                      List<unsigned int> odds,
                                      List<unsigned int> evens) {
  if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
    return std::make_pair(std::move(odds), std::move(evens));
  } else {
    const auto &[a0, a1] = std::get<typename List<unsigned int>::Cons>(l.v());
    if (Nat::even(a0)) {
      return collect_odds_evens(*a1, std::move(odds),
                                List<unsigned int>::cons(a0, std::move(evens)));
    } else {
      return collect_odds_evens(
          *a1, List<unsigned int>::cons(a0, std::move(odds)), std::move(evens));
    }
  }
}

std::pair<unsigned int, unsigned int>
FixStateThreading::sum_with_acc(const List<unsigned int> &l, unsigned int acc) {
  if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
    return std::make_pair(std::move(acc), 0u);
  } else {
    const auto &[a0, a1] = std::get<typename List<unsigned int>::Cons>(l.v());
    auto _cs = sum_with_acc(*a1, (std::move(acc) + a0));
    const unsigned int &acc_ = _cs.first;
    const unsigned int &s = _cs.second;
    return std::make_pair(std::move(_cs.first), (s + 1u));
  }
}

bool Nat::even(unsigned int n) {
  if (n <= 0) {
    return true;
  } else {
    unsigned int n0 = n - 1;
    if (n0 <= 0) {
      return false;
    } else {
      unsigned int n_ = n0 - 1;
      return Nat::even(n_);
    }
  }
}
