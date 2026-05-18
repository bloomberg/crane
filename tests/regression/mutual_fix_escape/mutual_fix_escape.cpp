#include "mutual_fix_escape.h"

/// Mutual fixpoint using fix...with...for syntax, then return
/// both functions through a pair.
std::pair<std::function<bool(uint64_t)>, std::function<bool(uint64_t)>>
MutualFixEscape::make_even_odd(uint64_t) {
  auto even_impl = [](auto &_self_even, auto &_self_odd, uint64_t n) -> bool {
    if (n <= 0) {
      return true;
    } else {
      uint64_t n_ = n - 1;
      return _self_odd(_self_even, _self_odd, n_);
    }
  };
  auto odd_impl = [](auto &_self_even, auto &_self_odd, uint64_t n) -> bool {
    if (n <= 0) {
      return false;
    } else {
      uint64_t n_ = n - 1;
      return _self_even(_self_even, _self_odd, n_);
    }
  };
  auto even = [=](uint64_t n) mutable -> bool {
    return even_impl(even_impl, odd_impl, n);
  };
  auto odd = [=](uint64_t n) mutable -> bool {
    return odd_impl(even_impl, odd_impl, n);
  };
  auto even0_impl = [](auto &_self_even0, auto &_self_odd0,
                       uint64_t n) -> bool {
    if (n <= 0) {
      return true;
    } else {
      uint64_t n_ = n - 1;
      return _self_odd0(_self_even0, _self_odd0, n_);
    }
  };
  auto odd0_impl = [](auto &_self_even0, auto &_self_odd0, uint64_t n) -> bool {
    if (n <= 0) {
      return false;
    } else {
      uint64_t n_ = n - 1;
      return _self_even0(_self_even0, _self_odd0, n_);
    }
  };
  auto even0 = [=](uint64_t n) mutable -> bool {
    return even0_impl(even0_impl, odd0_impl, n);
  };
  auto odd0 = [=](uint64_t n) mutable -> bool {
    return odd0_impl(even0_impl, odd0_impl, n);
  };
  return std::make_pair(even, odd0);
}

/// A mutual fixpoint that captures a parameter base.
std::pair<std::function<uint64_t(uint64_t)>, std::function<uint64_t(uint64_t)>>
MutualFixEscape::make_count_pair(uint64_t base) {
  auto count_even_impl = [=](auto &_self_count_even, auto &_self_count_odd,
                             uint64_t n) mutable -> uint64_t {
    if (n <= 0) {
      return base;
    } else {
      uint64_t n_ = n - 1;
      return (UINT64_C(1) +
              _self_count_odd(_self_count_even, _self_count_odd, n_));
    }
  };
  auto count_odd_impl = [=](auto &_self_count_even, auto &_self_count_odd,
                            uint64_t n) mutable -> uint64_t {
    if (n <= 0) {
      return (base * UINT64_C(2));
    } else {
      uint64_t n_ = n - 1;
      return (UINT64_C(1) +
              _self_count_even(_self_count_even, _self_count_odd, n_));
    }
  };
  auto count_even = [=](uint64_t n) mutable -> uint64_t {
    return count_even_impl(count_even_impl, count_odd_impl, n);
  };
  auto count_odd = [=](uint64_t n) mutable -> uint64_t {
    return count_odd_impl(count_even_impl, count_odd_impl, n);
  };
  auto count_even0_impl = [=](auto &_self_count_even0, auto &_self_count_odd0,
                              uint64_t n) mutable -> uint64_t {
    if (n <= 0) {
      return base;
    } else {
      uint64_t n_ = n - 1;
      return (UINT64_C(1) +
              _self_count_odd0(_self_count_even0, _self_count_odd0, n_));
    }
  };
  auto count_odd0_impl = [=](auto &_self_count_even0, auto &_self_count_odd0,
                             uint64_t n) mutable -> uint64_t {
    if (n <= 0) {
      return (base * UINT64_C(2));
    } else {
      uint64_t n_ = n - 1;
      return (UINT64_C(1) +
              _self_count_even0(_self_count_even0, _self_count_odd0, n_));
    }
  };
  auto count_even0 = [=](uint64_t n) mutable -> uint64_t {
    return count_even0_impl(count_even0_impl, count_odd0_impl, n);
  };
  auto count_odd0 = [=](uint64_t n) mutable -> uint64_t {
    return count_odd0_impl(count_even0_impl, count_odd0_impl, n);
  };
  return std::make_pair(count_even, count_odd0);
}
