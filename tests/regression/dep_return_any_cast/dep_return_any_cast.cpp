#include "dep_return_any_cast.h"

/// A definition with a dependent return type erases to std::any.  The
/// producer stores a List<uint64_t> but the consumer any_casts to
/// List<std::any>, so the program compiles and then dies at run time with
/// an uncaught std::bad_any_cast.
std::any DepReturnAnyCast::dep(bool b) {
  if (b) {
    return UINT64_C(7);
  } else {
    return List<std::any>::cons(
        UINT64_C(1), List<std::any>::cons(
                         UINT64_C(2), List<std::any>::cons(
                                          UINT64_C(3), List<std::any>::nil())));
  }
}

uint64_t DepReturnAnyCast::run(uint64_t k) {
  return ((std::any_cast<uint64_t>(dep(true)) +
           List<uint64_t>(std::any_cast<List<std::any>>(dep(false))).length()) +
          k);
}
