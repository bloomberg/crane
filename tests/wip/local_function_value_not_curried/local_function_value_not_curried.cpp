#include "local_function_value_not_curried.h"

List<crane::fn<uint64_t(uint64_t)>>
LocalFunctionValueNotCurried::from_fix(const List<uint64_t> &l) {
  auto mk_impl = [](auto &_self_mk, uint64_t n, uint64_t x) -> uint64_t {
    if (n <= 0) {
      return x;
    } else {
      uint64_t k = n - 1;
      return (_self_mk(_self_mk, k, x) + 1);
    }
  };
  auto mk = [=, mk_impl = std::move(mk_impl)](uint64_t n,
                                              uint64_t x) -> uint64_t {
    return mk_impl(mk_impl, n, x);
  };
  return l.template map<crane::fn<uint64_t(uint64_t)>>(std::move(mk));
}
