#ifndef INCLUDED_ANY_CAST_NESTED
#define INCLUDED_ANY_CAST_NESTED

#include <any>
#include <utility>
#include <variant>

template <typename A, typename P> struct SigT {
  // DATA
  A x;
  P a1;

  // ACCESSORS
  SigT<A, P> clone() const { return {x, a1}; }

  // CREATORS
  static SigT<A, P> existt(A x, P a1) { return {std::move(x), std::move(a1)}; }
};

struct AnyCastNested {
  template <typename a> using payload_ty = std::any;

  template <typename T1>
  static T1 extract_a(const SigT<uint64_t, payload_ty<T1>> &s) {
    const auto &[x0, a1] = s;
    if (x0 <= 0) {
      auto _cs = std::any_cast<std::pair<std::any, std::any>>(a1);
      const auto &_x = _cs.first;
      const auto &rest = _cs.second;
      auto _cs1 = std::any_cast<std::pair<std::any, std::any>>(rest);
      const auto &_x0 = _cs1.first;
      const T1 &v = _cs1.second;
      return std::any_cast<T1>(v);
    } else {
      uint64_t _x = x0 - 1;
      return std::any_cast<T1>(a1);
    }
  }

  static uint64_t test_extract(uint64_t x);
};

#endif // INCLUDED_ANY_CAST_NESTED
