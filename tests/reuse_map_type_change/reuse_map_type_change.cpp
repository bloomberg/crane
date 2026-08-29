#include "reuse_map_type_change.h"

ReuseMapTypeChange::lst<uint64_t>
ReuseMapTypeChange::build(uint64_t n, ReuseMapTypeChange::lst<uint64_t> acc) {
  if (n <= 0) {
    return acc;
  } else {
    uint64_t m = n - 1;
    return build(m, lst<uint64_t>::cons(n, std::move(acc)));
  }
}

uint64_t ReuseMapTypeChange::suml(const ReuseMapTypeChange::lst<uint64_t> &l) {
  if (std::holds_alternative<typename ReuseMapTypeChange::lst<uint64_t>::Nil>(
          l.v())) {
    return UINT64_C(0);
  } else {
    const auto &[a0, a1] =
        std::get<typename ReuseMapTypeChange::lst<uint64_t>::Cons>(l.v());
    return (a0 + suml(*a1));
  }
}

uint64_t ReuseMapTypeChange::go1(uint64_t n) {
  return suml(
      mapl<uint64_t, uint64_t>([](uint64_t x) { return (x + UINT64_C(1)); },
                               build(n, lst<uint64_t>::nil())));
}

uint64_t ReuseMapTypeChange::go2(uint64_t n) {
  return suml(mapl<ReuseMapTypeChange::lst<uint64_t>, uint64_t>(
      suml, mapl<uint64_t, ReuseMapTypeChange::lst<uint64_t>>(
                [](uint64_t x) {
                  return lst<uint64_t>::cons(
                      x, lst<uint64_t>::cons(x, lst<uint64_t>::nil()));
                },
                build(n, lst<uint64_t>::nil()))));
}
