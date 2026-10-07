#ifndef INCLUDED_PROMOTED_FIELD_CTOR_TARG_IN_LAMBDA
#define INCLUDED_PROMOTED_FIELD_CTOR_TARG_IN_LAMBDA

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include <atomic>
#include <concepts>
#include <memory>
#include <optional>
#include <stdexcept>
#include <utility>
#include <variant>

struct Nat;
template <typename A> struct List;
template <typename I>
concept Monad = requires {
  typename I::template m<crane::obj>;
  {
    I::template ret<crane::obj>(std::declval<crane::obj>())
  } -> std::convertible_to<typename I::template m<crane::obj>>;
  {
    I::template bind<crane::obj, crane::obj>(
        std::declval<typename I::template m<crane::obj>>(),
        std::declval<
            crane::fn<typename I::template m<crane::obj>(crane::obj)>>())
  } -> std::convertible_to<typename I::template m<crane::obj>>;
};

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

  Nat length() const {
    std::optional<Nat> _root{};
    std::shared_ptr<Nat> *_write = nullptr;
    const List<A> *_loop_self = this;
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
        auto _value = Nat::o();
        (_write ? *(*_write = std::make_shared<Nat>(std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[a0, a1] = std::get<typename List<A>::Cons>(_sv.v());
        auto _cell = typename Nat::S(nullptr);
        Nat &_node =
            (_write ? *(*_write = std::make_shared<Nat>(std::move(_cell)))
                    : _root.emplace(std::move(_cell)));
        _write = &std::get<typename Nat::S>(_node.v_mut()).a0;
        _loop_self = crane_raw(a1);
        continue;
      }
    }
    return std::move(*_root);
  }
};

struct Monad0 {
  template <Monad _tcI0, typename T2>
  static typename _tcI0::template m<T2> ret(const T2 &x);
  template <Monad _tcI0, typename T2, typename T3, typename F1>
  static typename _tcI0::template m<T3> bind(typename _tcI0::template m<T2> x,
                                             F1 &&x0);
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
    { I::size_of(std::declval<typename I::state>()) } -> std::convertible_to<Nat>;
  } && (requires {
    { I::initial_state() } -> std::convertible_to<typename I::state>;
  } || requires {
    { I::initial_state } -> std::convertible_to<typename I::state>;
  });

struct PromotedFieldCtorTargInLambda {
  using ptr = crane::obj;
  using state = crane::obj;

  template <typename S, typename X> struct memS {
    // TYPES
    struct Mret {
      X a0;
    };

    struct Mub {
      Nat a0;
    };

    struct Mget {
      crane::fn<memS<S, X>(S)> a0;
    };

    using variant_t = std::variant<Mret, Mub, Mget>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    memS() {}

    explicit memS(Mret _v) : v_(std::move(_v)) {}

    explicit memS(Mub _v) : v_(std::move(_v)) {}

    explicit memS(Mget _v) : v_(std::move(_v)) {}

    template <typename CraneU0, typename CraneU1>
    memS(const memS<CraneU0, CraneU1> &_other)
        : v_([&]() -> variant_t {
            if (std::holds_alternative<typename memS<CraneU0, CraneU1>::Mret>(
                    _other.v())) {
              const auto &[a0] =
                  std::get<typename memS<CraneU0, CraneU1>::Mret>(_other.v());
              return Mret{[&]() -> X {
                if constexpr (crane_convertible<X, const CraneU1 &>) {
                  return crane_convert<X>(a0);
                } else {
                  throw std::logic_error("unreachable: inactive constructor "
                                         "field at this instantiation");
                }
              }()};
            } else {
              if (std::holds_alternative<typename memS<CraneU0, CraneU1>::Mub>(
                      _other.v())) {
                const auto &[a0] =
                    std::get<typename memS<CraneU0, CraneU1>::Mub>(_other.v());
                return Mub{a0};
              } else {
                const auto &[a0] =
                    std::get<typename memS<CraneU0, CraneU1>::Mget>(_other.v());
                return Mget{crane_convert<crane::fn<memS<S, X>(S)>>(a0)};
              }
            }
          }()) {}

    static memS<S, X> mret(X a0) { return memS<S, X>(Mret{std::move(a0)}); }

    static memS<S, X> mub(Nat a0) { return memS<S, X>(Mub{std::move(a0)}); }

    static memS<S, X> mget(crane::fn<memS<S, X>(S)> a0) {
      return memS<S, X>(Mget{std::move(a0)});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename T2, typename T3>
  static T3 memS_rect(
      const std::type_identity_t<crane::fn<T3(T2)>> &f,
      const std::type_identity_t<crane::fn<T3(Nat)>> &f0,
      const std::type_identity_t<
          crane::fn<T3(crane::fn<memS<T1, T2>(T1)>, crane::fn<T3(T1)>)>> &f1,
      const memS<T1, T2> &m) {
    if (std::holds_alternative<typename memS<T1, T2>::Mret>(m.v())) {
      const auto &[a0] = std::get<typename memS<T1, T2>::Mret>(m.v());
      return f(a0);
    } else if (std::holds_alternative<typename memS<T1, T2>::Mub>(m.v())) {
      const auto &[a0] = std::get<typename memS<T1, T2>::Mub>(m.v());
      return f0(a0);
    } else {
      const auto &[a0] = std::get<typename memS<T1, T2>::Mget>(m.v());
      return f1(a0, [=](const T1 &y) {
        return memS_rect<T1, T2, T3>(f, f0, f1, a0(y));
      });
    }
  }

  template <typename T1, typename T2, typename T3, typename F0, typename F1,
            typename F2>
  static T3 memS_rec(F0 &&f, F1 &&f0, F2 &&f1, const memS<T1, T2> &m) {
    return memS_rect<T1, T2, T3>(f, f0, f1, m);
  }

  template <typename T1, typename T2, typename T3>
  static memS<T1, T3>
  memS_bind(const memS<T1, T2> &c,
            std::type_identity_t<crane::fn<memS<T1, T3>(T2)>> k) {
    if (std::holds_alternative<typename memS<T1, T2>::Mret>(c.v())) {
      const auto &[a0] = std::get<typename memS<T1, T2>::Mret>(c.v());
      return k(a0);
    } else if (std::holds_alternative<typename memS<T1, T2>::Mub>(c.v())) {
      const auto &[a0] = std::get<typename memS<T1, T2>::Mub>(c.v());
      return memS<T1, T3>::mub(a0);
    } else {
      const auto &[a0] = std::get<typename memS<T1, T2>::Mget>(c.v());
      return memS<T1, T3>::mget([=, k = std::move(k)](const T1 &s) {
        return memS_bind<T1, T2, T3>(a0(s), k);
      });
    }
  }

  template <typename T1> struct memS_mon {
    template <typename CraneA0> using m = memS<T1, CraneA0>;

    template <typename CraneA0> static memS<T1, CraneA0> ret(CraneA0 x) {
      return memS<T1, CraneA0>::mret(std::move(x));
    }

    template <typename CraneA0, typename CraneA1>
    static memS<T1, CraneA1> bind(memS<T1, CraneA0> a0,
                                  crane::fn<memS<T1, CraneA1>(CraneA0)> a1) {
      return memS_bind<T1, CraneA0, CraneA1>(std::move(a0), std::move(a1));
    }
  };

  template <typename T1> static const memS<T1, T1> &get() {
    static const memS<T1, T1> v =
        memS<T1, T1>::mget([](const auto &s) { return memS<T1, T1>::mret(s); });
    return v;
  }

  template <typename state, typename a> using memM = memS<state, a>;

  template <typename ptr> struct St {
    List<ptr> mem;
  };

  template <Params _tcI0> struct StateV {
    using ptr = typename _tcI0::ptr;
    using state = St<typename _tcI0::ptr>;

    static St<typename _tcI0::ptr> initial_state() {
      return St<typename _tcI0::ptr>{List<typename _tcI0::ptr>::nil()};
    }

    static Nat size_of(St<typename _tcI0::ptr> s) { return s.mem.length(); }
  };

  template <Params _tcI0>
  static memM<typename StateV<_tcI0>::state, Nat> read_size(const Nat &msg) {
    return memS_mon<St<typename _tcI0::ptr>>::template bind<
        St<typename _tcI0::ptr>, Nat>(
        get<St<typename _tcI0::ptr>>(),
        [=](const St<typename _tcI0::ptr> &s)
            -> memS<typename StateV<_tcI0>::state, Nat> {
          auto &&_sv = StateV<_tcI0>::size_of(s);
          if (std::holds_alternative<typename Nat::O>(_sv.v())) {
            return memS<typename StateV<_tcI0>::state, Nat>::mub(msg);
          } else {
            const auto &[a0] = std::get<typename Nat::S>(_sv.v());
            return memS_mon<St<typename _tcI0::ptr>>::template ret<Nat>(*a0);
          }
        });
  }

  template <Params _tcI0>
  static std::optional<Nat> run(const memS<St<typename _tcI0::ptr>, Nat> &m,
                                const St<typename _tcI0::ptr> &s) {
    if (std::holds_alternative<
            typename memS<St<typename _tcI0::ptr>, Nat>::Mret>(m.v())) {
      const auto &[a0] =
          std::get<typename memS<St<typename _tcI0::ptr>, Nat>::Mret>(m.v());
      return std::make_optional<Nat>(a0);
    } else if (std::holds_alternative<
                   typename memS<St<typename _tcI0::ptr>, Nat>::Mub>(m.v())) {
      return std::optional<Nat>();
    } else {
      const auto &[a0] =
          std::get<typename memS<St<typename _tcI0::ptr>, Nat>::Mget>(m.v());
      auto &&_sv0 = a0(s);
      if (std::holds_alternative<
              typename memS<St<typename _tcI0::ptr>, Nat>::Mret>(_sv0.v())) {
        const auto &[a00] =
            std::get<typename memS<St<typename _tcI0::ptr>, Nat>::Mret>(
                _sv0.v());
        return std::make_optional<Nat>(a00);
      } else {
        return std::optional<Nat>();
      }
    }
  }

  struct natParams {
    using ptr = Nat;

    static Nat zero() { return Nat::o(); }
  };

  static_assert(Params<natParams>);
  static inline const bool is_zero = []() -> bool {
    auto _cs = run<natParams>(
        read_size<natParams>(Nat::s(Nat::s(Nat::s(Nat::o())))),
        St<Nat>{List<Nat>::cons(Nat::s(Nat::o()), List<Nat>::nil())});
    if (_cs.has_value()) {
      const Nat &n = *_cs;
      return n.eqb(Nat::o());
    } else {
      return false;
    }
  }();
};

template <Monad _tcI0, typename T2>
typename _tcI0::template m<T2> Monad0::ret(const T2 &x) {
  return _tcI0::template ret<T2>(x);
}

template <Monad _tcI0, typename T2, typename T3, typename F1>
typename _tcI0::template m<T3> Monad0::bind(typename _tcI0::template m<T2> x,
                                            F1 &&x0) {
  return _tcI0::template bind<T2, T3>(std::move(x), x0);
}

#endif // INCLUDED_PROMOTED_FIELD_CTOR_TARG_IN_LAMBDA
