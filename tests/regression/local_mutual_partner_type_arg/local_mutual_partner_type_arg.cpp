#include "local_mutual_partner_type_arg.h"

/// A local mutual group whose partner g, not the member f the group is
/// projected to, takes a type argument.  Dummy elimination
/// (kill_dummy_fix) dropped the erased binders of the projected member
/// alone, and only where it had some, so g kept a parameter for A
/// while f's call to it, its dummy argument dropped, passed none: g
/// took one argument more than it was given.  Every member's erased
/// binders go, each member's calls adjusted.
uint64_t LocalMutualPartnerTypeArg::run(uint64_t, uint64_t n) {
  auto f_impl = [](auto &_self_f, auto &_self_g, uint64_t n0) -> uint64_t {
    if (n0 <= 0) {
      return UINT64_C(1);
    } else {
      uint64_t m = n0 - 1;
      return _self_g(
          _self_f, _self_g, [](uint64_t x) { return (x + UINT64_C(1)); }, m, m);
    }
  };
  auto g_impl = [](auto &_self_f, auto &_self_g,
                   const crane::fn<uint64_t(uint64_t)> &h, uint64_t x,
                   uint64_t n0) -> uint64_t {
    if (n0 <= 0) {
      return h(x);
    } else {
      uint64_t m = n0 - 1;
      return (_self_f(_self_f, _self_g, m) + UINT64_C(1));
    }
  };
  auto f = [&](uint64_t n0) -> uint64_t { return f_impl(f_impl, g_impl, n0); };
  auto g = [&](const crane::fn<uint64_t(uint64_t)> &h, uint64_t x,
               uint64_t n0) -> uint64_t {
    return g_impl(f_impl, g_impl, h, x, n0);
  };
  return f(n);
}
