#include "mem_safety_probe26.h"

MemSafetyProbe26::mylist<std::function<uint64_t(uint64_t)>>
MemSafetyProbe26::build_tree_closures(const MemSafetyProbe26::tree &t) {
  if (std::holds_alternative<typename MemSafetyProbe26::tree::Leaf>(t.v())) {
    return mylist<std::function<uint64_t(uint64_t)>>::mynil();
  } else {
    const auto &[a0, a1, a2] =
        std::get<typename MemSafetyProbe26::tree::Node>(t.v());
    const MemSafetyProbe26::tree &a0_value = *a0;
    const MemSafetyProbe26::tree &a2_value = *a2;
    return mylist<std::function<uint64_t(uint64_t)>>::mycons(
        [=](uint64_t x) mutable {
          return (((x + a0_value.tree_sum()) + a1) + a2_value.tree_sum());
        },
        mylist<std::function<uint64_t(uint64_t)>>::mynil());
  }
}

uint64_t MemSafetyProbe26::apply_first_closure(
    const MemSafetyProbe26::mylist<std::function<uint64_t(uint64_t)>> &l,
    uint64_t x) {
  if (std::holds_alternative<typename MemSafetyProbe26::mylist<
          std::function<uint64_t(uint64_t)>>::Mynil>(l.v())) {
    return x;
  } else {
    const auto &[a0, a1] = std::get<typename MemSafetyProbe26::mylist<
        std::function<uint64_t(uint64_t)>>::Mycons>(l.v());
    return a0(x);
  }
}
