#include <mutual_fix_escape.h>

#include <functional>
#include <type_traits>
#include <utility>

/// Mutual fixpoint using fix...with...for syntax, then return
/// both functions through a pair.
__attribute__((pure))
std::pair<std::function<bool(unsigned int)>, std::function<bool(unsigned int)>>
MutualFixEscape::make_even_odd(const unsigned int) {
  std::function<bool(unsigned int)> even;
  std::function<bool(unsigned int)> odd;
  even = [&](unsigned int n) -> bool {
    if (n <= 0) {
      return true;
    } else {
      unsigned int n_ = n - 1;
      return even(n_);
    }
  };
  odd = [&](unsigned int n) -> bool {
    if (n <= 0) {
      return false;
    } else {
      unsigned int n_ = n - 1;
      return odd(n_);
    }
  };
  std::function<bool(unsigned int)> even0;
  std::function<bool(unsigned int)> odd0;
  even0 = [&](unsigned int n) -> bool {
    if (n <= 0) {
      return true;
    } else {
      unsigned int n_ = n - 1;
      return even0(n_);
    }
  };
  odd0 = [&](unsigned int n) -> bool {
    if (n <= 0) {
      return false;
    } else {
      unsigned int n_ = n - 1;
      return odd0(n_);
    }
  };
  return std::make_pair(odd0, even0);
}

/// A mutual fixpoint that captures a parameter base.
__attribute__((pure)) std::pair<std::function<unsigned int(unsigned int)>,
                                std::function<unsigned int(unsigned int)>>
MutualFixEscape::make_count_pair(const unsigned int base) {
  std::function<unsigned int(unsigned int)> count_even;
  std::function<unsigned int(unsigned int)> count_odd;
  count_even = [&](unsigned int n) -> unsigned int {
    if (n <= 0) {
      return base;
    } else {
      unsigned int n_ = n - 1;
      return (1u + count_even(n_));
    }
  };
  count_odd = [&](unsigned int n) -> unsigned int {
    if (n <= 0) {
      return (base * 2u);
    } else {
      unsigned int n_ = n - 1;
      return (1u + count_odd(n_));
    }
  };
  std::function<unsigned int(unsigned int)> count_even0;
  std::function<unsigned int(unsigned int)> count_odd0;
  count_even0 = [&](unsigned int n) -> unsigned int {
    if (n <= 0) {
      return count_odd;
    } else {
      unsigned int n_ = n - 1;
      return (1u + count_even0(n_));
    }
  };
  count_odd0 = [&](unsigned int n) -> unsigned int {
    if (n <= 0) {
      return (count_odd * 2u);
    } else {
      unsigned int n_ = n - 1;
      return (1u + count_odd0(n_));
    }
  };
  return std::make_pair(count_odd0, count_even0);
}
