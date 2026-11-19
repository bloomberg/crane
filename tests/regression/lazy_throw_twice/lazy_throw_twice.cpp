#include "lazy_throw_twice.h"

uint64_t LazyThrowTwice::boom(const List<uint64_t> &) {
  throw std::logic_error(
      "unrealized axiom: "
      "CraneTestsRegression.lazy_throw_twice.LazyThrowTwice.LazyThrowTwice.boom");
}

LazyThrowTwice::stream LazyThrowTwice::after(const List<uint64_t> &l) {
  return stream::lazy_(
      [=,
       l = l]() mutable -> typename LazyThrowTwice::stream::SCons {
        return {boom(l), after(List<uint64_t>::cons(l.length(), l))};
      });
}

LazyThrowTwice::stream LazyThrowTwice::upto(uint64_t n,
                                            const List<uint64_t> &l) {
  if (n <= 0) {
    return after(l);
  } else {
    uint64_t m = n - 1;
    return stream::lazy_(
        [=,
         l = l]() mutable -> typename LazyThrowTwice::stream::SCons {
          return {l.length(), upto(m, List<uint64_t>::cons(n, l))};
        });
  }
}

uint64_t LazyThrowTwice::hd(const LazyThrowTwice::stream &s) {
  const auto &[a0, _] = std::get<typename LazyThrowTwice::stream::SCons>(s.v());
  return a0;
}

LazyThrowTwice::stream LazyThrowTwice::tl(const LazyThrowTwice::stream &s) {
  const auto &[_, a1] = std::get<typename LazyThrowTwice::stream::SCons>(s.v());
  return a1;
}

LazyThrowTwice::stream LazyThrowTwice::sample() {
  return upto(
      UINT64_C(1),
      List<uint64_t>::cons(
          UINT64_C(1),
          List<uint64_t>::cons(
              UINT64_C(2),
              List<uint64_t>::cons(UINT64_C(3), List<uint64_t>::nil()))));
}
