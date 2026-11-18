#include "pos_sub_saturates.h"

/// positive has no zero: Rocq's Pos.sub x y is 1 when x <= y, and
/// Pos.pred 1 is 1.  Mapping.NInt printed both as plain unsigned
/// subtraction, so Pos.sub 2 5 wrapped around and Pos.pred 1 was 0.
unsigned int PosSubSaturates::s(unsigned int x0_, unsigned int x1_) {
  return (x0_ > x1_ ? x0_ - x1_ : 1u);
}

unsigned int PosSubSaturates::p(unsigned int x0_) {
  return (x0_ > 1u ? x0_ - 1u : 1u);
}
