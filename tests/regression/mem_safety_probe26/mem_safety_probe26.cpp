#include "mem_safety_probe26.h"

MemSafetyProbe26::mylist<std::function<unsigned int(unsigned int)>>
MemSafetyProbe26::build_tree_closures(const MemSafetyProbe26::tree &t) {
  if (std::holds_alternative<typename MemSafetyProbe26::tree::Leaf>(t.v())) {
    return mylist<std::function<unsigned int(unsigned int)>>::mynil();
  } else {
    const auto &[d_a0, d_a1, d_a2] =
        std::get<typename MemSafetyProbe26::tree::Node>(t.v());
    MemSafetyProbe26::tree d_a0_value = *d_a0;
    MemSafetyProbe26::tree d_a2_value = *d_a2;
    return mylist<std::function<unsigned int(unsigned int)>>::mycons(
        [=](unsigned int x) mutable {
          return (((x + d_a0_value.tree_sum()) + d_a1) + d_a2_value.tree_sum());
        },
        mylist<std::function<unsigned int(unsigned int)>>::mynil());
  }
}

unsigned int MemSafetyProbe26::apply_first_closure(
    const MemSafetyProbe26::mylist<std::function<unsigned int(unsigned int)>>
        &l,
    unsigned int x) {
  if (std::holds_alternative<typename MemSafetyProbe26::mylist<
          std::function<unsigned int(unsigned int)>>::Mynil>(l.v())) {
    return x;
  } else {
    const auto &[d_a0, d_a1] = std::get<typename MemSafetyProbe26::mylist<
        std::function<unsigned int(unsigned int)>>::Mycons>(l.v());
    return d_a0(x);
  }
}
