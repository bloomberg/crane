#include "dep_type_fn_any_cast.h"

DepTypeFnAnyCast::dt DepTypeFnAnyCast::mk(uint64_t n) {
  if (n <= 0) {
    return UINT64_C(5);
  } else {
    uint64_t _x = n - 1;
    return List<crane::obj>::cons(
        UINT64_C(1),
        List<crane::obj>::cons(
            UINT64_C(2),
            List<crane::obj>::cons(
                UINT64_C(3),
                List<crane::obj>::cons(UINT64_C(4), List<crane::obj>::nil()))));
  }
}

uint64_t DepTypeFnAnyCast::run(uint64_t k) {
  return ((crane::any_cast<uint64_t>(mk(UINT64_C(0))) +
           List<uint64_t>(crane::any_cast<List<crane::obj>>(mk(UINT64_C(1))))
               .length()) +
          k);
}
