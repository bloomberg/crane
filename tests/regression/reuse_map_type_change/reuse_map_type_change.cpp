#include "reuse_map_type_change.h"

/// Reuse bug: the Perceus reuse pass recycles a cell of the *input* type to
/// build a value of the *output* type.
///
/// For a type-changing map : (A -> B) -> lst A -> lst B, the cons arm
/// rebuilds lst B while the recycled cell belongs to lst A, so codegen
/// emits
///
/// return lst<T2>::cons__reuse(std::move(std::get<1>(l.v_mut()).a1), ...)
/// ^ crane::rc<lst<T1>>, parameter wants
/// crane::rc<lst<T2>>
///
/// and clang rejects it ("no viable conversion"). The types are not merely
/// inconvenient: lst<A> and lst<B> have different size, alignment and
/// destructor, so constructing one in the other's storage would be undefined
/// behaviour even if the token were castable. The reuse candidate search
/// never checks that the matched inductive and the rebuilt constructor agree
/// on their type arguments.
///
/// go1 (A = B = nat) compiles, so the failure needs a map that actually
/// changes the element type. Removing Set Crane Reuse. makes the file
/// compile.
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
