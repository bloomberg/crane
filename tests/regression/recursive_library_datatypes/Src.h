#ifndef INCLUDED_SRC
#define INCLUDED_SRC

#include <cstdint>
#include <type_traits>
#include <variant>

#include "Datatypes.h"

namespace Src {

struct T;

struct T {
  // DATA
  uint64_t a0;

  // ACCESSORS
  T clone() const { return {a0}; }

  // CREATORS
  static T t0(uint64_t a0) { return {a0}; }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, const uint64_t &>
  T1 t_rect(F0 &&f) const {
    const auto &[a0] = *this;
    return f(a0);
  }

  template <typename T1, typename F0> T1 t_rec(F0 &&f) const {
    return this->template t_rect<T1>(f);
  }

  uint64_t get() const {
    const auto &[a0] = *this;
    return a0;
  }
};

const uint64_t r =
    (T::t0(UINT64_C(4)).get() +
     Datatypes::template List<uint64_t>::cons(
         UINT64_C(1),
         Datatypes::template List<uint64_t>::cons(
             UINT64_C(2), Datatypes::template List<uint64_t>::nil()))
         .length());

} // namespace Src

#endif // INCLUDED_SRC
