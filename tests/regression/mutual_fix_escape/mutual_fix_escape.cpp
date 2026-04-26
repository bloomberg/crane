#include <mutual_fix_escape.h>

#include <functional>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>

/// Mutual fixpoint using fix...with...for syntax, then return
/// both functions through a pair.
__attribute__((pure))
std::pair<std::function<bool(unsigned int)>, std::function<bool(unsigned int)>>
MutualFixEscape::make_even_odd(const unsigned int &) {
  auto even = std::make_shared<std::function<bool(unsigned int)>>();
  auto odd = std::make_shared<std::function<bool(unsigned int)>>();
  *even = [=](unsigned int n) mutable -> bool {
    if (n <= 0) {
      return true;
    } else {
      unsigned int n_ = n - 1;
      return (*odd)(n_);
    }
  };
  *odd = [=](unsigned int n) mutable -> bool {
    if (n <= 0) {
      return false;
    } else {
      unsigned int n_ = n - 1;
      return (*even)(n_);
    }
  };
  auto even0 = std::make_shared<std::function<bool(unsigned int)>>();
  auto odd0 = std::make_shared<std::function<bool(unsigned int)>>();
  *even0 = [=](unsigned int n) mutable -> bool {
    if (n <= 0) {
      return true;
    } else {
      unsigned int n_ = n - 1;
      return (*odd0)(n_);
    }
  };
  *odd0 = [=](unsigned int n) mutable -> bool {
    if (n <= 0) {
      return false;
    } else {
      unsigned int n_ = n - 1;
      return (*even0)(n_);
    }
  };
  return std::make_pair((*even), (*odd0));
}

/// A mutual fixpoint that captures a parameter base.
__attribute__((pure)) std::pair<std::function<unsigned int(unsigned int)>,
                                std::function<unsigned int(unsigned int)>>
MutualFixEscape::make_count_pair(unsigned int base) {
  auto count_even =
      std::make_shared<std::function<unsigned int(unsigned int)>>();
  auto count_odd =
      std::make_shared<std::function<unsigned int(unsigned int)>>();
  *count_even = [=](unsigned int n) mutable -> unsigned int {
    if (n <= 0) {
      return base;
    } else {
      unsigned int n_ = n - 1;
      return (1u + (*count_odd)(n_));
    }
  };
  *count_odd = [=](unsigned int n) mutable -> unsigned int {
    if (n <= 0) {
      return (base * 2u);
    } else {
      unsigned int n_ = n - 1;
      return (1u + (*count_even)(n_));
    }
  };
  auto count_even0 =
      std::make_shared<std::function<unsigned int(unsigned int)>>();
  auto count_odd0 =
      std::make_shared<std::function<unsigned int(unsigned int)>>();
  *count_even0 = [=](unsigned int n) mutable -> unsigned int {
    if (n <= 0) {
      return base;
    } else {
      unsigned int n_ = n - 1;
      return (1u + (*count_odd0)(n_));
    }
  };
  *count_odd0 = [=](unsigned int n) mutable -> unsigned int {
    if (n <= 0) {
      return (base * 2u);
    } else {
      unsigned int n_ = n - 1;
      return (1u + (*count_even0)(n_));
    }
  };
  return std::make_pair((*count_even), (*count_odd0));
}
