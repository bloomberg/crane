#ifndef INCLUDED_FUNCTOR_PARAM_CUSTOM_LIST
#define INCLUDED_FUNCTOR_PARAM_CUSTOM_LIST

#include <concepts>
#include <cstdint>
#include <deque>

/// A functor's parameter type inside a custom-mapped type: R.String is
/// list R.Sigma, and list is a custom.  Extraction carried the type
/// argument R.Sigma among the custom's term arguments too, and the
/// custom's conversion read it as a value -- a callee no callable plan
/// exists for, an anomaly once a missing plan became one.  From ParseALot,
/// whose Matcher parameter R.Ty.Sigma stopped its extraction.
template <typename M>
concept T = requires {
  typename M::Sigma;
  { M::ok(std::declval<typename M::Sigma>()) } -> std::same_as<bool>;
  typename M::String;
};

struct FunctorParamCustomList {
  template <T R> struct Impl {
    static bool all_ok(const std::deque<typename R::Sigma> &s) {
      if (s.empty()) {
        return true;
      } else {
        const auto &x = s.front();
        std::deque<typename R::Sigma> xs(s.begin() + 1, s.end());
        return (R::ok(x) && all_ok(xs));
      }
    }
  };

  struct Digits {
    using Sigma = uint64_t;
    static bool ok(uint64_t n);
    using String = std::deque<Sigma>;
  };

  using DigitsImpl = Impl<Digits>;
  static bool all_digits(const std::deque<uint64_t> &x0_);
};

#endif // INCLUDED_FUNCTOR_PARAM_CUSTOM_LIST
