#pragma once

struct PrimFloat {
  static inline const double infinity = __builtin_inf();
  static inline const double nan = __builtin_nan("");
};

struct PrimFloatSelfInit {
  static inline const double inf = PrimFloat::infinity;
  static inline const double not_a_number = PrimFloat::nan;
  static inline const double ordinary = 0x1p-1;
};
