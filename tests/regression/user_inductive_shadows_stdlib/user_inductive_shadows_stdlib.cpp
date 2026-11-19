#include "user_inductive_shadows_stdlib.h"

/// A user inductive called Comparison and the standard library's
/// comparison (returned by Nat.compare) are emitted under the same C++
/// name, and the later declaration wins.  The match on Nat.compare's result
/// then looks for LT in the user's type: "no member named 'LT' in
/// 'UserInductiveShadowsStdlib::Comparison'".  The two types are unrelated in
/// Rocq; only their emitted names collide.
uint64_t
UserInductiveShadowsStdlib::mine(UserInductiveShadowsStdlib::Comparison c) {
  switch (c) {
  case Comparison::LT_: {
    return UINT64_C(0);
  }
  case Comparison::EQ_: {
    return UINT64_C(1);
  }
  case Comparison::GT_: {
    return UINT64_C(2);
  }
  default:
    std::unreachable();
  }
}

uint64_t UserInductiveShadowsStdlib::theirs(uint64_t a, uint64_t b) {
  switch ((a < b ? ::Comparison::LT
                 : (b < a ? ::Comparison::GT : ::Comparison::EQ))) {
  case ::Comparison::EQ: {
    return UINT64_C(1);
  }
  case ::Comparison::LT: {
    return UINT64_C(0);
  }
  case ::Comparison::GT: {
    return UINT64_C(2);
  }
  default:
    std::unreachable();
  }
}

/// The standard comparison named as a type inside the struct, where the
/// bare name finds the user's Comparison.
::Comparison UserInductiveShadowsStdlib::theirs_cmp(uint64_t a, uint64_t b) {
  if (a == b) {
    return ::Comparison::EQ;
  } else {
    return ::Comparison::LT;
  }
}
