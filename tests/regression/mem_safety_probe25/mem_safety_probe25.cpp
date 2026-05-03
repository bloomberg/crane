#include <mem_safety_probe25.h>

MemSafetyProbe25::mylist<std::function<unsigned int(unsigned int)>>
MemSafetyProbe25::build_adders(const MemSafetyProbe25::tree &t) {
  if (std::holds_alternative<typename MemSafetyProbe25::tree::Leaf>(t.v())) {
    return mylist<std::function<unsigned int(unsigned int)>>::mynil();
  } else {
    const auto &[d_a0, d_a1, d_a2] =
        std::get<typename MemSafetyProbe25::tree::Node>(t.v());
    return mylist<std::function<unsigned int(unsigned int)>>::mycons(
        [=](const unsigned int x) mutable { return (x + d_a1); },
        mylist<std::function<unsigned int(unsigned int)>>::mynil());
  }
}

unsigned int MemSafetyProbe25::apply_first(
    const MemSafetyProbe25::mylist<std::function<unsigned int(unsigned int)>>
        &l,
    const unsigned int x) {
  if (std::holds_alternative<typename MemSafetyProbe25::mylist<
          std::function<unsigned int(unsigned int)>>::Mynil>(l.v())) {
    return x;
  } else {
    const auto &[d_a0, d_a1] = std::get<typename MemSafetyProbe25::mylist<
        std::function<unsigned int(unsigned int)>>::Mycons>(l.v());
    return d_a0(x);
  }
}
