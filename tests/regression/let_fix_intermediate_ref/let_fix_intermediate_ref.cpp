#include "let_fix_intermediate_ref.h"

uint64_t LetFixIntermediateRef::sum_heads(const List<List<uint64_t>> &ll) {
  auto go_impl = [](auto &_self_go, const List<List<uint64_t>> &xss,
                    uint64_t acc) -> uint64_t {
    if (std::holds_alternative<typename List<List<uint64_t>>::Nil>(xss.v())) {
      return acc;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<List<uint64_t>>::Cons>(xss.v());
      uint64_t hd = [&]() {
        if (std::holds_alternative<typename List<uint64_t>::Nil>(a0.v())) {
          return UINT64_C(0);
        } else {
          const auto &[a00, a10] =
              std::get<typename List<uint64_t>::Cons>(a0.v());
          return a00;
        }
      }();
      return _self_go(_self_go, *a1, (acc + hd));
    }
  };
  auto go = [&](const List<List<uint64_t>> &xss, uint64_t acc) -> uint64_t {
    return go_impl(go_impl, xss, acc);
  };
  return go(ll, UINT64_C(0));
}

uint64_t LetFixIntermediateRef::zip_sum(const List<uint64_t> &l1,
                                        const List<uint64_t> &l2) {
  if (std::holds_alternative<typename List<uint64_t>::Nil>(l1.v())) {
    return UINT64_C(0);
  } else {
    const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l1.v());
    if (std::holds_alternative<typename List<uint64_t>::Nil>(l2.v())) {
      return UINT64_C(0);
    } else {
      const auto &[a00, a10] = std::get<typename List<uint64_t>::Cons>(l2.v());
      return ((a0 + a00) + zip_sum(*a1, *a10));
    }
  }
}
