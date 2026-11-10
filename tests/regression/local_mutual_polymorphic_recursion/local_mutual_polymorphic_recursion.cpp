#include "local_mutual_polymorphic_recursion.h"

/// The local version of mutual_lambda_other_instance: f calls its
/// partner g at bool, not at the list nat it is entered at, and g
/// passes the lambda back to f.  Extraction types a local group's bodies
/// at one instance, which would type f's callable over List and g's
/// over bool, with no conversion from one to the other.  Instead the
/// group's type binders are erased (Extraction.erased_fix_types): both
/// callables are crane::fn<uint64_t(crane::obj)>, a closure written at its
/// own instance is adapted by crane_erase_fn, and g passes h back
/// unadapted, as it is already erased.
uint64_t LocalMutualPolymorphicRecursion::run(uint64_t n) {
  static const auto erased_fn =
      crane::immortal(crane_erase_fn<uint64_t>([](bool b) {
        if (b) {
          return UINT64_C(10);
        } else {
          return UINT64_C(20);
        }
      }));
  auto f_impl = [&](auto &_self_f, auto &_self_g,
                    const crane::fn<uint64_t(crane::obj)> &h, crane::obj y,
                    uint64_t n0) -> uint64_t {
    if (n0 <= 0) {
      return h(y);
    } else {
      uint64_t m = n0 - 1;
      return _self_g(_self_f, _self_g, erased_fn, true, m);
    }
  };
  auto g_impl = [](auto &_self_f, auto &_self_g,
                   const crane::fn<uint64_t(crane::obj)> &h, crane::obj x,
                   uint64_t n0) -> uint64_t {
    if (n0 <= 0) {
      return (h(x) + UINT64_C(1));
    } else {
      uint64_t m = n0 - 1;
      return _self_f(_self_f, _self_g, h, x, m);
    }
  };
  auto f = [&](const crane::fn<uint64_t(crane::obj)> &h, crane::obj y,
               uint64_t n0) -> uint64_t {
    return f_impl(f_impl, g_impl, h, y, n0);
  };
  auto g = [&](const crane::fn<uint64_t(crane::obj)> &h, crane::obj x,
               uint64_t n0) -> uint64_t {
    return g_impl(f_impl, g_impl, h, x, n0);
  };
  return f(crane_erase_fn<uint64_t>(
               [](const List<uint64_t> &_x) { return _x.length(); }),
           List<crane::obj>::cons(
               UINT64_C(1),
               List<crane::obj>::cons(
                   UINT64_C(2), List<crane::obj>::cons(
                                    UINT64_C(3), List<crane::obj>::nil()))),
           n);
}
