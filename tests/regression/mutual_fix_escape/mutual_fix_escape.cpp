#include <mutual_fix_escape.h>

/// Mutual fixpoint using fix...with...for syntax, then return
/// both functions through a pair.
std::pair<std::function<bool(unsigned int)>, std::function<bool(unsigned int)>>
MutualFixEscape::make_even_odd(const unsigned int &) {
  auto even_impl = [](auto &_self_even, auto &_self_odd,
                      unsigned int n) -> bool {
    if (n <= 0) {
      return true;
    } else {
      unsigned int n_ = n - 1;
      return _self_odd(_self_even, _self_odd, n_);
    }
  };
  auto odd_impl = [](auto &_self_even, auto &_self_odd,
                     unsigned int n) -> bool {
    if (n <= 0) {
      return false;
    } else {
      unsigned int n_ = n - 1;
      return _self_even(_self_even, _self_odd, n_);
    }
  };
  auto even = [=](unsigned int n) mutable -> bool {
    return even_impl(even_impl, odd_impl, n);
  };
  auto odd = [=](unsigned int n) mutable -> bool {
    return odd_impl(even_impl, odd_impl, n);
  };
  auto even0_impl = [](auto &_self_even0, auto &_self_odd0,
                       unsigned int n) -> bool {
    if (n <= 0) {
      return true;
    } else {
      unsigned int n_ = n - 1;
      return _self_odd0(_self_even0, _self_odd0, n_);
    }
  };
  auto odd0_impl = [](auto &_self_even0, auto &_self_odd0,
                      unsigned int n) -> bool {
    if (n <= 0) {
      return false;
    } else {
      unsigned int n_ = n - 1;
      return _self_even0(_self_even0, _self_odd0, n_);
    }
  };
  auto even0 = [=](unsigned int n) mutable -> bool {
    return even0_impl(even0_impl, odd0_impl, n);
  };
  auto odd0 = [=](unsigned int n) mutable -> bool {
    return odd0_impl(even0_impl, odd0_impl, n);
  };
  return std::make_pair(even, odd0);
}

/// A mutual fixpoint that captures a parameter base.
std::pair<std::function<unsigned int(unsigned int)>,
          std::function<unsigned int(unsigned int)>>
MutualFixEscape::make_count_pair(unsigned int base) {
  auto count_even_impl = [=](auto &_self_count_even, auto &_self_count_odd,
                             unsigned int n) mutable -> unsigned int {
    if (n <= 0) {
      return base;
    } else {
      unsigned int n_ = n - 1;
      return (1u + _self_count_odd(_self_count_even, _self_count_odd, n_));
    }
  };
  auto count_odd_impl = [=](auto &_self_count_even, auto &_self_count_odd,
                            unsigned int n) mutable -> unsigned int {
    if (n <= 0) {
      return (base * 2u);
    } else {
      unsigned int n_ = n - 1;
      return (1u + _self_count_even(_self_count_even, _self_count_odd, n_));
    }
  };
  auto count_even = [=](unsigned int n) mutable -> unsigned int {
    return count_even_impl(count_even_impl, count_odd_impl, n);
  };
  auto count_odd = [=](unsigned int n) mutable -> unsigned int {
    return count_odd_impl(count_even_impl, count_odd_impl, n);
  };
  auto count_even0_impl = [=](auto &_self_count_even0, auto &_self_count_odd0,
                              unsigned int n) mutable -> unsigned int {
    if (n <= 0) {
      return base;
    } else {
      unsigned int n_ = n - 1;
      return (1u + _self_count_odd0(_self_count_even0, _self_count_odd0, n_));
    }
  };
  auto count_odd0_impl = [=](auto &_self_count_even0, auto &_self_count_odd0,
                             unsigned int n) mutable -> unsigned int {
    if (n <= 0) {
      return (base * 2u);
    } else {
      unsigned int n_ = n - 1;
      return (1u + _self_count_even0(_self_count_even0, _self_count_odd0, n_));
    }
  };
  auto count_even0 = [=](unsigned int n) mutable -> unsigned int {
    return count_even0_impl(count_even0_impl, count_odd0_impl, n);
  };
  auto count_odd0 = [=](unsigned int n) mutable -> unsigned int {
    return count_odd0_impl(count_even0_impl, count_odd0_impl, n);
  };
  return std::make_pair(count_even, count_odd0);
}
