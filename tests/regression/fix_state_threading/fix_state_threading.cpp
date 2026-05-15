#include "fix_state_threading.h"

std::pair<List<unsigned int>, unsigned int>
FixStateThreading::reverse_count(const List<unsigned int> &l,
                                 List<unsigned int> acc) {
  if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
    return std::make_pair(std::move(acc), 0u);
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename List<unsigned int>::Cons>(l.v());
    auto _cs = reverse_count(*(d_a1), List<unsigned int>::cons(d_a0, acc));
    const List<unsigned int> &acc_ = _cs.first;
    const unsigned int &n = _cs.second;
    return std::make_pair(acc_, (n + 1u));
  }
}

std::pair<List<unsigned int>, List<unsigned int>>
FixStateThreading::collect_odds_evens(const List<unsigned int> &l,
                                      List<unsigned int> odds,
                                      List<unsigned int> evens) {
  if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
    return std::make_pair(std::move(odds), std::move(evens));
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename List<unsigned int>::Cons>(l.v());
    if (Nat::even(d_a0)) {
      return collect_odds_evens(
          *(d_a1), std::move(odds),
          List<unsigned int>::cons(d_a0, std::move(evens)));
    } else {
      return collect_odds_evens(*(d_a1),
                                List<unsigned int>::cons(d_a0, std::move(odds)),
                                std::move(evens));
    }
  }
}

std::pair<unsigned int, unsigned int>
FixStateThreading::sum_with_acc(const List<unsigned int> &l,
                                const unsigned int acc) {
  if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
    return std::make_pair(acc, 0u);
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename List<unsigned int>::Cons>(l.v());
    auto _cs = sum_with_acc(*(d_a1), (acc + d_a0));
    const unsigned int &acc_ = _cs.first;
    const unsigned int &s = _cs.second;
    return std::make_pair(acc_, (s + 1u));
  }
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
      return Nat::even(n_);
    }
  }
}
