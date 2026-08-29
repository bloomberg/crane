#include "eta_closure_first_class.h"

/// A definition whose body is a let followed by a lambda is eta-expanded
/// into a two-argument C++ function.  Passing it first-class to map then
/// fails, because a uint64_t(uint64_t, uint64_t) is not convertible to
/// std::function<uint64_t(uint64_t)>.
uint64_t EtaClosureFirstClass::mkclosure(uint64_t n, uint64_t _x0) {
  return [=]() mutable {
    List<uint64_t> big = ListDef::template repeat<uint64_t>(n, UINT64_C(100));
    return [=](uint64_t k) mutable {
      return (k + big.template fold_left<uint64_t>(
                      [](uint64_t _x0, uint64_t _x1) -> uint64_t {
                        return (_x0 + _x1);
                      },
                      UINT64_C(0)));
    };
  }()(_x0);
}

uint64_t EtaClosureFirstClass::run(uint64_t k) {
  List<std::function<uint64_t(uint64_t)>> fs =
      List<uint64_t>::cons(
          UINT64_C(1),
          List<uint64_t>::cons(
              UINT64_C(2),
              List<uint64_t>::cons(UINT64_C(3), List<uint64_t>::nil())))
          .template map<std::function<uint64_t(uint64_t)>>([](uint64_t _ec0) {
            return [=](uint64_t _ec1) mutable { return mkclosure(_ec0, _ec1); };
          });
  return std::move(fs).template fold_left<uint64_t>(
      [](uint64_t a, std::function<uint64_t(uint64_t)> f) { return f(a); }, k);
}
