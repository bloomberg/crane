#ifndef INCLUDED_USER_INDUCTIVE_SHADOWS_STDLIB
#define INCLUDED_USER_INDUCTIVE_SHADOWS_STDLIB

#include <utility>

enum class Comparison;

struct Nat {
  static Comparison compare(uint64_t n, uint64_t m);
};
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

  static uint64_t mine(Comparison c);
  static uint64_t theirs(uint64_t a, uint64_t b);
  static inline const uint64_t run =
      (mine(Comparison::EQ_) + theirs(UINT64_C(1), UINT64_C(2)));
};

#endif // INCLUDED_USER_INDUCTIVE_SHADOWS_STDLIB
