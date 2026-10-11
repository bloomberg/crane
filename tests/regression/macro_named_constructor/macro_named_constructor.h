#ifndef INCLUDED_MACRO_NAMED_CONSTRUCTOR
#define INCLUDED_MACRO_NAMED_CONSTRUCTOR

#include <cmath>
#include <cstdint>
#include <utility>

enum class Float_class;
enum class Float_class {
  PNORMAL,
  NNORMAL,
  PSUBN,
  NSUBN,
  PZERO,
  NZERO_,
  PINF,
  NINF,
  NAN_
};

struct MacroNamedConstructor {
  enum class Num { NAN_, INFINITY_, EOF_, NULL_, ERRNO };

  template <typename T1>
  static T1 num_rect(T1 f, T1 f0, T1 f1, T1 f2, T1 f3, Num n) {
    switch (n) {
    case Num::NAN_: {
      return f;
    }
    case Num::INFINITY_: {
      return f0;
    }
    case Num::EOF_: {
      return f1;
    }
    case Num::NULL_: {
      return f2;
    }
    case Num::ERRNO: {
      return f3;
    }
    default:
      std::unreachable();
    }
  }

  template <typename T1>
  static T1 num_rec(T1 f, T1 f0, T1 f1, T1 f2, T1 f3, Num n) {
    return num_rect<T1>(std::move(f), std::move(f0), std::move(f1),
                        std::move(f2), std::move(f3), n);
  }

  static uint64_t code(Num n);
  static inline const uint64_t total = (code(Num::EOF_) + code(Num::ERRNO));
  /// The standard library's own float_class has a NAN constructor.
  static bool is_normal(double f);
  static inline const bool two_is_normal = is_normal(0x1.4p+1);
};

#endif // INCLUDED_MACRO_NAMED_CONSTRUCTOR
