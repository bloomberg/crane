#pragma once

#include <cstdint>
#include <utility>

enum class Comparison;
enum class Comparison { EQ, LT, GT };

/// A user inductive called Comparison and the standard library's
/// comparison (returned by Nat.compare) are emitted under the same C++
/// name, and the later declaration wins.  The match on Nat.compare's result
/// then looks for LT in the user's type: "no member named 'LT' in
/// 'UserInductiveShadowsStdlib::Comparison'".  The two types are unrelated in
/// Rocq; only their emitted names collide.
struct UserInductiveShadowsStdlib {
  enum class Comparison { LT_, EQ_, GT_ };

  template <typename T1>
  static T1 Comparison_rect(T1 f, T1 f0, T1 f1, Comparison c) {
    switch (c) {
    case Comparison::LT_: {
      return f;
    }
    case Comparison::EQ_: {
      return f0;
    }
    case Comparison::GT_: {
      return f1;
    }
    default:
      std::unreachable();
    }
  }

  template <typename T1>
  static T1 Comparison_rec(T1 f, T1 f0, T1 f1, Comparison c) {
    return Comparison_rect<T1>(std::move(f), std::move(f0), std::move(f1), c);
  }

  static uint64_t mine(Comparison c);
  static uint64_t theirs(uint64_t a, uint64_t b);
  /// The standard comparison named as a type inside the struct, where the
  /// bare name finds the user's Comparison.
  static ::Comparison theirs_cmp(uint64_t a, uint64_t b);
  static inline const uint64_t run =
      mine(Comparison::EQ_) + theirs(UINT64_C(1), UINT64_C(2)) + []() {
        switch (theirs_cmp(UINT64_C(3), UINT64_C(3))) {
        case ::Comparison::EQ: {
          return UINT64_C(10);
        }
        default: {
          return UINT64_C(0);
        }
        }
      }();
};
