#include "local_fix_parameter_names.h"

uint64_t LocalFixParameterNames::walk2(uint64_t f, List<uint64_t> x0_) {
  auto f0_impl = [&](auto &_self_f0, auto &_self_g,
                     const List<uint64_t> &l) -> uint64_t {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
      return f;
    } else {
      const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
      return _self_g(_self_f0, _self_g, *a1);
    }
  };
  auto g_impl = [&](auto &_self_f0, auto &_self_g,
                    const List<uint64_t> &) -> uint64_t {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(f1.v())) {
      return (f + UINT64_C(1));
    } else {
      const auto &[a00, a10] = std::get<typename List<uint64_t>::Cons>(f1.v());
      return _self_f0(_self_f0, _self_g, *a10);
    }
  };
  auto f0 = [&](const List<uint64_t> &l) -> uint64_t {
    return f0_impl(f0_impl, g_impl, l);
  };
  auto g = [&](const List<uint64_t> &f0) -> uint64_t {
    return g_impl(f0_impl, g_impl, f0);
  };
  return f0(std::move(x0_));
}
