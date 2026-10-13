#ifndef INCLUDED_RECORD_AT_SORT_TYPE_FIELD
#define INCLUDED_RECORD_AT_SORT_TYPE_FIELD

#include "crane_fn.h"
#include "obj.h"
#include <cstdint>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

struct RecordAtSortTypeField {
  template <typename A> struct wrap {
    A unwrap;

    // ACCESSORS
    template <typename CraneU> operator wrap<CraneU>() const {
      return {[&]() -> CraneU {
        if constexpr (crane_convertible<CraneU, const A &>) {
          return crane_convert<CraneU>(unwrap);
        } else {
          throw std::logic_error(
              "unreachable: inactive constructor field at this instantiation");
        }
      }()};
    }
  };

  static inline const wrap<crane::obj> w = wrap<crane::obj>{crane::obj()};

  template <typename A, typename B> struct pair {
    A pfst;
    B psnd;

    // ACCESSORS
    template <typename CraneU0, typename CraneU1>
    operator pair<CraneU0, CraneU1>() const {
      return {[&]() -> CraneU0 {
                if constexpr (crane_convertible<CraneU0, const A &>) {
                  return crane_convert<CraneU0>(pfst);
                } else {
                  throw std::logic_error("unreachable: inactive constructor "
                                         "field at this instantiation");
                }
              }(),
              [&]() -> CraneU1 {
                if constexpr (crane_convertible<CraneU1, const B &>) {
                  return crane_convert<CraneU1>(psnd);
                } else {
                  throw std::logic_error("unreachable: inactive constructor "
                                         "field at this instantiation");
                }
              }()};
    }
  };

  static inline const pair<crane::obj, crane::obj> tp =
      pair<crane::obj, crane::obj>{crane::obj(), crane::obj()};

  template <typename A, typename B> struct pr {
    // DATA
    A a0;
    B a1;

    // ACCESSORS
    pr<A, B> clone() const { return {a0, a1}; }

    template <typename CraneU0, typename CraneU1>
    operator pr<CraneU0, CraneU1>() const {
      return {[&]() -> CraneU0 {
                if constexpr (crane_convertible<CraneU0, const A &>) {
                  return crane_convert<CraneU0>(a0);
                } else {
                  throw std::logic_error("unreachable: inactive constructor "
                                         "field at this instantiation");
                }
              }(),
              [&]() -> CraneU1 {
                if constexpr (crane_convertible<CraneU1, const B &>) {
                  return crane_convert<CraneU1>(a1);
                } else {
                  throw std::logic_error("unreachable: inactive constructor "
                                         "field at this instantiation");
                }
              }()};
    }

    // CREATORS
    static pr<A, B> p(A a0, B a1) { return {std::move(a0), std::move(a1)}; }
  };

  template <typename T1, typename T2, typename T3, typename F0>
    requires std::is_invocable_r_v<T3, F0 &, const T1 &, const T2 &>
  static T3 pr_rect(F0 &&f, const pr<T1, T2> &p0) {
    const auto &[a0, a1] = p0;
    return f(a0, a1);
  }

  template <typename T1, typename T2, typename T3, typename F0>
  static T3 pr_rec(F0 &&f, const pr<T1, T2> &p0) {
    return pr_rect<T1, T2, T3>(f, p0);
  }

  static inline const pr<crane::obj, uint64_t> p =
      pr<crane::obj, uint64_t>::p(crane::obj(), UINT64_C(3));

  static inline const uint64_t result = []() {
    const auto &_sv = p;
    const auto &[a0, a1] = _sv;
    return a1;
  }();
};

#endif // INCLUDED_RECORD_AT_SORT_TYPE_FIELD
