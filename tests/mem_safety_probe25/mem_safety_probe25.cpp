#include "mem_safety_probe25.h"

MemSafetyProbe25::mylist<std::function<uint64_t(uint64_t)>>
MemSafetyProbe25::build_adders(const MemSafetyProbe25::tree &t) {
  if (std::holds_alternative<typename MemSafetyProbe25::tree::Leaf>(t.v())) {
    return mylist<std::function<uint64_t(uint64_t)>>::mynil();
  } else {
    const auto &[a0, a1, a2] =
        std::get<typename MemSafetyProbe25::tree::Node>(t.v());
    return mylist<std::function<uint64_t(uint64_t)>>::mycons(
        [=](uint64_t x) mutable { return (x + a1); },
        mylist<std::function<uint64_t(uint64_t)>>::mynil());
  }
}

uint64_t MemSafetyProbe25::apply_first(
    const MemSafetyProbe25::mylist<std::function<uint64_t(uint64_t)>> &l,
    uint64_t x) {
  if (std::holds_alternative<typename MemSafetyProbe25::mylist<
          std::function<uint64_t(uint64_t)>>::Mynil>(l.v())) {
    return x;
  } else {
    const auto &[a0, a1] = std::get<typename MemSafetyProbe25::mylist<
        std::function<uint64_t(uint64_t)>>::Mycons>(l.v());
    return a0(x);
  }
}
