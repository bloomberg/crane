#ifndef INCLUDED_TYPE_INDEXED_INDUCTIVE_PROBE
#define INCLUDED_TYPE_INDEXED_INDUCTIVE_PROBE

#include "crane_fn.h"
#include <any>
#include <utility>
#include <variant>

enum class Bool0 { TRUE_, FALSE_ };

struct TypeIndexedInductiveProbe {
  struct wrap {
    // DATA
    std::any a;

    // ACCESSORS
    wrap clone() const { return {a}; }

    // CREATORS
    static wrap wrap0(std::any a) { return {std::move(a)}; }
  };

  template <typename T1, typename T2, typename F0>
  static T1 wrap_rect(F0 &&f, const wrap &w0) {
    const auto &[a0] = w0;
    return std::any_cast<T1>(crane_call_erased(f, std::any_cast<T2>(a0)));
  }

  template <typename T1, typename T2, typename F0>
  static T1 wrap_rec(F0 &&f, const wrap &w0) {
    const auto &[a0] = w0;
    return std::any_cast<T1>(crane_call_erased(f, std::any_cast<T2>(a0)));
  }

  static inline const wrap w = wrap::wrap0(Bool0::TRUE_);
  static inline const Bool0 sample = []() {
    const auto &_sv0 = w;
    const auto &[a0] = _sv0;
    return std::any_cast<Bool0>(a0);
  }();
};

#endif // INCLUDED_TYPE_INDEXED_INDUCTIVE_PROBE
