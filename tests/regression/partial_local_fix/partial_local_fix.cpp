#include "partial_local_fix.h"

Nat PartialLocalFix::run(Bool0 _x0) {
  return []() {
    auto loop_impl = [](auto &_self_loop, Nat n, Bool0 b) -> Nat {
      if (std::holds_alternative<typename Nat::O>(n.v())) {
        return Nat::o();
      } else {
        const auto &[a0] = std::get<typename Nat::S>(n.v());
        switch (b) {
        case Bool0::TRUE_: {
          return Nat::s(_self_loop(_self_loop, *a0, b));
        }
        case Bool0::FALSE_: {
          return _self_loop(_self_loop, *a0, b);
        }
        default:
          std::unreachable();
        }
      }
    };
    auto loop = [=](Nat n, Bool0 b) mutable -> Nat {
      return loop_impl(loop_impl, n, b);
    };
    return [=](Bool0 _pa0) mutable {
      return loop(Nat::s(Nat::s(Nat::s(
                      Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::o())))))))),
                  _pa0);
    };
  }()(_x0);
}
