#pragma once

struct Pos {
}; /// positive has no zero: Rocq's Pos.sub x y is 1 when x <= y, and

/// Pos.pred 1 is 1.  Mapping.NInt printed both as plain unsigned
/// subtraction, so Pos.sub 2 5 wrapped around and Pos.pred 1 was 0.
struct PosSubSaturates {
  static unsigned int s(unsigned int x0_, unsigned int x1_);
  static unsigned int p(unsigned int x0_);
  static inline const unsigned int t =
      ((2u * 1u) > (2u * (2u * 1u) + 1u) ? (2u * 1u) - (2u * (2u * 1u) + 1u)
                                         : 1u);
};
