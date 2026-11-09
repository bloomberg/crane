#include "local_mutual_polymorphic_recursion.h"

/// The local version of mutual_lambda_other_instance: f calls its
/// partner g at bool, not at the list nat it is entered at, and g
/// passes the lambda back to f.  Extraction types a local group's bodies
/// at one instance, so the group is not lifted (it has no type variables
/// of its own) and its lambdas take f's callable at
/// crane::fn<uint64_t(List<uint64_t>)> and g's at
/// crane::fn<uint64_t(bool)>: g's call back to f has no conversion.
/// No C++.  No infinite instantiation can arise here: the callables are
/// crane::fn already.
uint64_t LocalMutualPolymorphicRecursion::run(uint64_t n) {
  auto f_impl = [](auto &_self_f, auto &_self_g,
                   const crane::fn<uint64_t(List<uint64_t>)> &h,
                   const List<uint64_t> &y, uint64_t n0) -> uint64_t {
    if (n0 <= 0) {
      return h(y);
    } else {
      uint64_t m = n0 - 1;
      return _self_g(
          _self_f, _self_g,
          [](bool b) -> uint64_t {
            if (b) {
              return UINT64_C(10);
            } else {
              return UINT64_C(20);
            }
          },
          true, m);
    }
  };
  auto g_impl = [](auto &_self_f, auto &_self_g,
                   const crane::fn<uint64_t(bool)> &h, bool x,
                   uint64_t n0) -> uint64_t {
    if (n0 <= 0) {
      return (h(x) + UINT64_C(1));
    } else {
      uint64_t m = n0 - 1;
      return _self_f(_self_f, _self_g, h, x, m);
    }
  };
  auto f = [&](const crane::fn<uint64_t(List<uint64_t>)> &h,
               const List<uint64_t> &y, uint64_t n0) -> uint64_t {
    return f_impl(f_impl, g_impl, h, y, n0);
  };
  auto g = [&](const crane::fn<uint64_t(bool)> &h, bool x,
               uint64_t n0) -> uint64_t {
    return g_impl(f_impl, g_impl, h, x, n0);
  };
  return f([](const List<uint64_t> &_x) { return _x.length(); },
           List<uint64_t>::cons(
               UINT64_C(1),
               List<uint64_t>::cons(
                   UINT64_C(2),
                   List<uint64_t>::cons(UINT64_C(3), List<uint64_t>::nil()))),
           n);
}
