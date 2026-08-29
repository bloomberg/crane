#include "dep_type_fn_any_cast.h"

DepTypeFnAnyCast::dt DepTypeFnAnyCast::mk(uint64_t n) {
  if (n <= 0) {
    return UINT64_C(5);
  } else {
    uint64_t _x = n - 1;
    return List<std::any>::cons(
        UINT64_C(1),
        List<std::any>::cons(
            UINT64_C(2),
            List<std::any>::cons(
                UINT64_C(3),
                List<std::any>::cons(UINT64_C(4), List<std::any>::nil()))));
  }
}

uint64_t DepTypeFnAnyCast::run(uint64_t k) {
  return ((std::any_cast<uint64_t>(mk(UINT64_C(0))) +
           List<uint64_t>(std::any_cast<List<std::any>>(mk(UINT64_C(1))))
               .length()) +
          k);
}
