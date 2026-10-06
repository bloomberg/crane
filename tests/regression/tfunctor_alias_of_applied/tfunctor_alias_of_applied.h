#ifndef INCLUDED_TFUNCTOR_ALIAS_OF_APPLIED
#define INCLUDED_TFUNCTOR_ALIAS_OF_APPLIED

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include <atomic>
#include <concepts>
#include <memory>
#include <optional>
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

  Nat add(Nat m) const {
    std::optional<Nat> _root{};
    std::shared_ptr<Nat> *_write = nullptr;
    const Nat *_loop_self = this;
    Nat _loop_m = std::move(m);
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename Nat::O>(_sv.v())) {
        auto _value = std::move(_loop_m);
        (_write ? *(*_write = std::make_shared<Nat>(std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[a0] = std::get<typename Nat::S>(_sv.v());
        auto _cell = typename Nat::S(nullptr);
        Nat &_node =
            (_write ? *(*_write = std::make_shared<Nat>(std::move(_cell)))
                    : _root.emplace(std::move(_cell)));
        _write = &std::get<typename Nat::S>(_node.v_mut()).a0;
        _loop_self = crane_raw(a0);
        continue;
      }
    }
    return std::move(*_root);
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

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, const A &>
  List<T1> map(F0 &&f) const {
    std::optional<List<T1>> _root{};
    std::shared_ptr<List<T1>> *_write = nullptr;
    const List<A> *_loop_self = this;
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
        auto _value = List<T1>::nil();
        (_write ? *(*_write = std::make_shared<List<T1>>(std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[a0, a1] = std::get<typename List<A>::Cons>(_sv.v());
        auto _cell = typename List<T1>::Cons(f(a0), nullptr);
        List<T1> &_node =
            (_write ? *(*_write = std::make_shared<List<T1>>(std::move(_cell)))
                    : _root.emplace(std::move(_cell)));
        _write = &std::get<typename List<T1>::Cons>(_node.v_mut()).l;
        _loop_self = crane_raw(a1);
        continue;
      }
    }
    return std::move(*_root);
  }
};

template <typename I>
concept TFunctor = requires {
  typename I::template T<crane::obj>;
  {
    I::template tfmap<crane::obj, crane::obj>(
        std::declval<crane::fn<crane::obj(crane::obj)>>(),
        std::declval<typename I::template T<crane::obj>>())
  } -> std::convertible_to<typename I::template T<crane::obj>>;
};
template <typename I>
concept ConvertTyp = requires {
  typename I::template F<crane::obj>;
  {
    I::convert_typ(std::declval<Nat>(),
                   std::declval<typename I::template F<Nat>>())
  } -> std::convertible_to<typename I::template F<Nat>>;
};

struct TfunctorAliasOfApplied {
  template <TFunctor _tcI0, typename T2, typename T3, typename F0>
  static typename _tcI0::template T<T3>
  tfmap(F0 &&f, typename _tcI0::template T<T2> x) {
    return _tcI0::template tfmap<T2, T3>(f, std::move(x));
  }

  struct TFunctor_list {
    template <typename CraneA0> using T = List<CraneA0>;

    template <typename CraneA0, typename CraneA1>
    static List<CraneA1> tfmap(crane::fn<CraneA1(CraneA0)> a0,
                               List<CraneA0> a1) {
      return a1.template map<CraneA1>(std::move(a0));
    }
  };

  static_assert(TFunctor<TFunctor_list>);

  template <TFunctor _tcI0> struct TFunctor_list_ {
    template <typename CraneA0>
    using T = List<typename _tcI0::template T<CraneA0>>;

    template <typename CraneA0, typename CraneA1>
    static List<typename _tcI0::template T<CraneA1>>
    tfmap(crane::fn<CraneA1(CraneA0)> f,
          List<typename _tcI0::template T<CraneA0>> a0) {
      return a0.template map<typename _tcI0::template T<CraneA1>>(
          [=, f = std::move(f)](typename _tcI0::template T<CraneA0> a1) {
            return _tcI0::template tfmap<CraneA0, CraneA1>(f, a1);
          });
    }
  };

  template <typename T> struct cfg {
    T blk;

    // ACCESSORS
    template <typename CraneU> operator cfg<CraneU>() const {
      return {[&]() -> CraneU {
        if constexpr (crane_convertible<CraneU, const T &>) {
          return crane_convert<CraneU>(blk);
        } else {
          throw std::logic_error(
              "unreachable: inactive constructor field at this instantiation");
        }
      }()};
    }
  };

  template <typename T, typename FnBody> struct definition {
    T df_ty;
    FnBody df_body;

    // ACCESSORS
    template <typename CraneU0, typename CraneU1>
    operator definition<CraneU0, CraneU1>() const {
      return {[&]() -> CraneU0 {
                if constexpr (crane_convertible<CraneU0, const T &>) {
                  return crane_convert<CraneU0>(df_ty);
                } else {
                  throw std::logic_error("unreachable: inactive constructor "
                                         "field at this instantiation");
                }
              }(),
              [&]() -> CraneU1 {
                if constexpr (crane_convertible<CraneU1, const FnBody &>) {
                  return crane_convert<CraneU1>(df_body);
                } else {
                  throw std::logic_error("unreachable: inactive constructor "
                                         "field at this instantiation");
                }
              }()};
    }
  };

  template <typename T, typename FnBody> struct modul {
    List<definition<T, FnBody>> m_defs;

    // ACCESSORS
    template <typename CraneU0, typename CraneU1>
    operator modul<CraneU0, CraneU1>() const {
      return {crane_convert<List<definition<CraneU0, CraneU1>>>(m_defs)};
    }
  };

  template <typename t> using mcfg = modul<t, cfg<t>>;

  struct TFunctor_cfg {
    template <typename CraneA0> using T = cfg<CraneA0>;

    template <typename CraneA0, typename CraneA1>
    static cfg<CraneA1> tfmap(crane::fn<CraneA1(CraneA0)> f, cfg<CraneA0> c) {
      return cfg<CraneA1>{f(std::move(c).blk)};
    }
  };

  static_assert(TFunctor<TFunctor_cfg>);

  template <TFunctor _tcI0> struct TFunctor_definition {
    template <typename CraneA0>
    using T = definition<CraneA0, typename _tcI0::template T<CraneA0>>;

    template <typename CraneA0, typename CraneA1>
    static definition<CraneA1, typename _tcI0::template T<CraneA1>>
    tfmap(crane::fn<CraneA1(CraneA0)> f,
          definition<CraneA0, typename _tcI0::template T<CraneA0>> d) {
      return definition<CraneA1, typename _tcI0::template T<CraneA1>>{
          f(d.df_ty), _tcI0::template tfmap<CraneA0, CraneA1>(f, d.df_body)};
    }
  };

  template <TFunctor _tcI0, TFunctor _tcI1> struct TFunctor_mcfg {
    template <typename CraneA0>
    using T = modul<CraneA0, typename _tcI0::template T<CraneA0>>;

    template <typename CraneA0, typename CraneA1>
    static modul<CraneA1, typename _tcI0::template T<CraneA1>>
    tfmap(crane::fn<CraneA1(CraneA0)> f,
          modul<CraneA0, typename _tcI0::template T<CraneA0>> p) {
      return modul<CraneA1, typename _tcI0::template T<CraneA1>>{
          TFunctor_list_<_tcI1>::template tfmap<CraneA0, CraneA1>(
              std::move(f), std::move(p).m_defs)};
    }
  };

  template <ConvertTyp _tcI0>
  static typename _tcI0::template F<Nat>
  convert_typ(const Nat &x0_, typename _tcI0::template F<Nat> x1_) {
    return _tcI0::convert_typ(x0_, std::move(x1_));
  }

  struct ConvertTyp_mcfg {
    template <typename CraneA0> using F = mcfg<CraneA0>;

    static mcfg<Nat> convert_typ(Nat k, mcfg<Nat> a0) {
      return TFunctor_mcfg<TFunctor_cfg, TFunctor_definition<TFunctor_cfg>>::
          template tfmap<Nat, Nat>(
              [=, k = std::move(k)](const Nat &n) { return n.add(k); },
              std::move(a0));
    }
  };

  static_assert(ConvertTyp<ConvertTyp_mcfg>);
  static mcfg<Nat> convert(const modul<Nat, cfg<Nat>> &m);
  static inline const mcfg<Nat> m0 =
      modul<Nat, cfg<Nat>>{List<definition<Nat, cfg<Nat>>>::cons(
          definition<Nat, cfg<Nat>>{Nat::s(Nat::o()),
                                    cfg<Nat>{Nat::s(Nat::s(Nat::o()))}},
          List<definition<Nat, cfg<Nat>>>::nil())};
  static inline const Nat total = []() {
    auto &&_sv = convert(m0).m_defs;
    if (std::holds_alternative<typename List<definition<Nat, cfg<Nat>>>::Nil>(
            _sv.v())) {
      return Nat::o();
    } else {
      const auto &[a0, a1] =
          std::get<typename List<definition<Nat, cfg<Nat>>>::Cons>(_sv.v());
      return a0.df_ty.add(a0.df_body.blk);
    }
  }();
  static inline const bool is_five =
      total.eqb(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::o()))))));
};

#endif // INCLUDED_TFUNCTOR_ALIAS_OF_APPLIED
