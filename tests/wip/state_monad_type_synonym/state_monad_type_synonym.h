#ifndef INCLUDED_STATE_MONAD_TYPE_SYNONYM
#define INCLUDED_STATE_MONAD_TYPE_SYNONYM

#include <functional>
#include <type_traits>
#include <utility>

/// WIP: A state-monad type synonym (`st A := nat -> (A * nat)`) used through
/// `bind` produces a call with the wrong arity on the `std::function` synonym.
struct StateMonadTypeSynonym {
  template <typename a>
  using st = std::function<std::pair<a, uint64_t>(uint64_t)>;

  template <typename T1> static st<T1> ret(T1 a) {
    return [=](uint64_t s) mutable { return std::make_pair(a, s); };
  }

  template <typename T1, typename T2, typename F1>
    requires std::is_invocable_r_v<st<T2>, F1 &, T1 &>
  static st<T2> bind(st<T1> m, F1 &&f) {
    return [=](uint64_t s) mutable {
      std::pair<T1, uint64_t> p = m(s);
      return f(p.first)(p.second);
    };
  }

  static inline const st<uint64_t> tick = [](uint64_t s) {
    return std::make_pair(s, (s + 1));
  };
  static inline const st<uint64_t> prog = []() {
    return bind<uint64_t, uint64_t>(tick, [](uint64_t a) {
      return bind<uint64_t, uint64_t>(
          tick, [=](uint64_t b) mutable { return ret<uint64_t>((a + b)); });
    });
  }();
  static inline const uint64_t go = prog()(UINT64_C(1)).first;
};

#endif // INCLUDED_STATE_MONAD_TYPE_SYNONYM
