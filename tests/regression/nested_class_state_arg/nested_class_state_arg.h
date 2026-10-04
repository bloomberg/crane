#ifndef INCLUDED_NESTED_CLASS_STATE_ARG
#define INCLUDED_NESTED_CLASS_STATE_ARG

#include "crane_fn.h"
#include "obj.h"
#include <atomic>
#include <concepts>
#include <memory>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

struct Nat;
template <typename A> struct List;

struct Nat {
  // TYPES
  struct O {};

  struct S {
    std::shared_ptr<Nat> a0;
  };

  using variant_t = std::variant<O, S>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Nat() {}

  explicit Nat(O _v) : v_(_v) {}

  explicit Nat(S _v) : v_(std::move(_v)) {}

  static Nat o() { return Nat(O{}); }

  static Nat s(Nat a0) { return Nat(S{std::make_shared<Nat>(std::move(a0))}); }

  // MANIPULATORS
  ~Nat() {
    auto _next = [&](variant_t &_v) -> std::shared_ptr<Nat> {
      if (auto *_alt = std::get_if<S>(&_v)) {
        if (_alt->a0 && _alt->a0.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          return std::move(_alt->a0);
        }
      }
      return nullptr;
    };
    std::shared_ptr<Nat> _cur = _next(v_mut());
    while (_cur) {
      _cur = _next(_cur->v_mut());
    }
  }

  Nat(const Nat &) = default;
  Nat &operator=(const Nat &) = default;
  Nat(Nat &&) = default;
  Nat &operator=(Nat &&) = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  bool eqb(const Nat &m) const {
    const Nat *_loop_self = this;
    const Nat *_loop_m = &m;
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename Nat::O>(_sv.v())) {
        if (std::holds_alternative<typename Nat::O>(_loop_m->v())) {
          return true;
        } else {
          return false;
        }
      } else {
        const auto &[a0] = std::get<typename Nat::S>(_sv.v());
        if (std::holds_alternative<typename Nat::O>(_loop_m->v())) {
          return false;
        } else {
          const auto &[a00] = std::get<typename Nat::S>(_loop_m->v());
          _loop_self = crane_raw(a0);
          _loop_m = crane_raw(a00);
        }
      }
    }
  }
};

template <typename A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    A a;
    std::shared_ptr<List<A>> l;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  List() {}

  explicit List(Nil _v) : v_(_v) {}

  explicit List(Cons _v) : v_(std::move(_v)) {}

  template <typename CraneU>
  List(const List<CraneU> &_other)
      : v_([&]() -> variant_t {
          if (std::holds_alternative<typename List<CraneU>::Nil>(_other.v())) {
            return Nil{};
          } else {
            const auto &[a, l] =
                std::get<typename List<CraneU>::Cons>(_other.v());
            return Cons{
                [&]() -> A {
                  if constexpr (crane_convertible<A, const CraneU &>) {
                    return crane_convert<A>(a);
                  } else {
                    throw std::logic_error("unreachable: inactive constructor "
                                           "field at this instantiation");
                  }
                }(),
                (l ? std::make_shared<List<A>>(crane_convert<List<A>>(*l))
                   : nullptr)};
          }
        }()) {}

  static List<A> nil() { return List<A>(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List<A>(Cons{std::move(a), std::make_shared<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  ~List() {
    auto _next = [&](variant_t &_v) -> std::shared_ptr<List<A>> {
      if (auto *_alt = std::get_if<Cons>(&_v)) {
        if (_alt->l && _alt->l.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          return std::move(_alt->l);
        }
      }
      return nullptr;
    };
    std::shared_ptr<List<A>> _cur = _next(v_mut());
    while (_cur) {
      _cur = _next(_cur->v_mut());
    }
  }

  List(const List &) = default;
  List &operator=(const List &) = default;
  List(List &&) = default;
  List &operator=(List &&) = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

template <typename
I>concept Params = requires {
    typename I::ptr;
  } && (requires {
    { I::zero() } -> std::convertible_to<typename I::ptr>;
  } || requires {
    { I::zero } -> std::convertible_to<typename I::ptr>;
  });
template <typename
I>concept MemState = requires {
    typename I::state;
  } && (requires {
    { I::initial_state() } -> std::convertible_to<typename I::state>;
  } || requires {
    { I::initial_state } -> std::convertible_to<typename I::state>;
  });
template <typename I>
concept MemPrims = requires {
  typename I::mm_state;
  { I::bump(std::declval<Nat>()) } -> std::convertible_to<Nat>;
};

struct NestedClassStateArg {
  using ptr = crane::obj;
  using state = crane::obj;

  template <typename ptr> struct St {
    List<ptr> mem;
  };

  template <Params _tcI0> struct MemStateV {
    using ptr = typename _tcI0::ptr;
    using state = St<typename _tcI0::ptr>;

    static St<typename _tcI0::ptr> initial_state() {
      return St<typename _tcI0::ptr>{List<typename _tcI0::ptr>::nil()};
    }
  };

  template <Params _tcI0> struct MemPrimsV {
    using mm_state = MemStateV<_tcI0>;
    using ptr = typename _tcI0::ptr;
    using state = typename mm_state::state;

    static Nat bump(Nat x) { return Nat::s(std::move(x)); }
  };

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<Nat, F0 &, T1 &>
  static Nat run_st(F0 &&f, T1 x0_) {
    return f(std::move(x0_));
  }

  template <typename ptr>
  using FusedS = std::pair<St<ptr>, std::pair<List<Nat>, Nat>>;

  template <Params _tcI0> static Nat interp_it(FusedS<typename _tcI0::ptr> s) {
    return run_st<FusedS<typename _tcI0::ptr>>(
        [](FusedS<typename _tcI0::ptr> st) { return (st.second).second; },
        std::move(s));
  }

  template <Params _tcI0> static Nat start(std::monostate) {
    return interp_it<_tcI0>(std::make_pair(
        MemStateV<_tcI0>::initial_state(),
        std::make_pair(List<Nat>::cons(Nat::s(Nat::o()),
                                       List<Nat>::cons(Nat::s(Nat::s(Nat::o())),
                                                       List<Nat>::nil())),
                       Nat::s(Nat::s(Nat::s(Nat::o()))))));
  }

  struct natParams {
    using ptr = Nat;

    static Nat zero() { return Nat::o(); }
  };

  static_assert(Params<natParams>);
  static inline const bool is_three =
      start<natParams>(std::monostate{}).eqb(Nat::s(Nat::s(Nat::s(Nat::o()))));
};

#endif // INCLUDED_NESTED_CLASS_STATE_ARG
