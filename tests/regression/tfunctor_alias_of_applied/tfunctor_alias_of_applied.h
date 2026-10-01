#ifndef INCLUDED_TFUNCTOR_ALIAS_OF_APPLIED
#define INCLUDED_TFUNCTOR_ALIAS_OF_APPLIED

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include <any>
#include <atomic>
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
  Nat(Nat &&) noexcept = default;
  Nat &operator=(Nat &&) noexcept = default;

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
    std::shared_ptr<Nat> _head{};
    std::shared_ptr<Nat> *_write = &_head;
    const Nat *_loop_self = this;
    Nat _loop_m = std::move(m);
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename Nat::O>(_sv.v())) {
        *_write = std::make_shared<Nat>(std::move(_loop_m));
        break;
      } else {
        const auto &[a0] = std::get<typename Nat::S>(_sv.v());
        auto _cell = std::make_shared<Nat>(typename Nat::S(nullptr));
        *_write = std::move(_cell);
        _write = &std::get<typename Nat::S>((*_write)->v_mut()).a0;
        _loop_self = crane_raw(a0);
        continue;
      }
    }
    return std::move(*_head);
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

  template <typename _U>
  List(const List<_U> &_other)
      : v_([&]() -> variant_t {
          if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
            return Nil{};
          } else {
            const auto &[a, l] = std::get<typename List<_U>::Cons>(_other.v());
            return Cons{
                [&]() -> A {
                  if constexpr (crane_convertible<A, const _U &>) {
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
  List(List &&) noexcept = default;
  List &operator=(List &&) noexcept = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, A &>
  List<T1> map(F0 &&f) const {
    std::shared_ptr<List<T1>> _head{};
    std::shared_ptr<List<T1>> *_write = &_head;
    const List<A> *_loop_self = this;
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
        *_write = std::make_shared<List<T1>>(List<T1>::nil());
        break;
      } else {
        const auto &[a0, a1] = std::get<typename List<A>::Cons>(_sv.v());
        auto _cell =
            std::make_shared<List<T1>>(typename List<T1>::Cons(f(a0), nullptr));
        *_write = std::move(_cell);
        _write = &std::get<typename List<T1>::Cons>((*_write)->v_mut()).l;
        _loop_self = crane_raw(a1);
        continue;
      }
    }
    return std::move(*_head);
  }
};

struct TfunctorAliasOfApplied {
  template <typename t>
  using TFunctor = crane::fn<t(crane::fn<crane::obj(crane::obj)>, t)>;

  template <typename T1, typename T2, typename T3, typename F1>
  static crane::rebind_t<T1, T3>
  tfmap(std::type_identity_t<TFunctor<T1>> tFunctor, F1 &&f,
        crane::rebind_t<T1, T2> x) {
    return crane_container_cast<crane::rebind_t<T1, T3>>(
        tFunctor(crane_erase_fn(f), crane_convert<T1>(std::move(x))));
  }

  static List<crane::obj> TFunctor_list(crane::fn<crane::obj(crane::obj)> x0_,
                                        const List<crane::obj> &x1_);

  template <typename T1, typename F1>
  static List<T1> TFunctor_list_(std::type_identity_t<TFunctor<T1>> h, F1 &&f,
                                 List<T1> x0_) {
    return std::move(x0_).template map<T1>([=](T1 _x0) -> T1 {
      return tfmap<T1, crane::obj, crane::obj>(h, f, _x0);
    });
  }

  template <typename T> struct cfg {
    T blk;

    // ACCESSORS
    template <typename _U> operator cfg<_U>() const {
      return {[&]() -> _U {
        if constexpr (crane_convertible<_U, const T &>) {
          return crane_convert<_U>(blk);
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
    template <typename _U0, typename _U1>
    operator definition<_U0, _U1>() const {
      return {[&]() -> _U0 {
                if constexpr (crane_convertible<_U0, const T &>) {
                  return crane_convert<_U0>(df_ty);
                } else {
                  throw std::logic_error("unreachable: inactive constructor "
                                         "field at this instantiation");
                }
              }(),
              [&]() -> _U1 {
                if constexpr (crane_convertible<_U1, const FnBody &>) {
                  return crane_convert<_U1>(df_body);
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
    template <typename _U0, typename _U1> operator modul<_U0, _U1>() const {
      return {crane_convert<List<definition<_U0, _U1>>>(m_defs)};
    }
  };

  template <typename t> using mcfg = modul<t, cfg<t>>;
  static cfg<crane::obj> TFunctor_cfg(crane::fn<crane::obj(crane::obj)> f,
                                      const cfg<crane::obj> &c);

  template <typename T1, typename F1>
  static definition<crane::obj, T1>
  TFunctor_definition(std::type_identity_t<TFunctor<T1>> h, F1 &&f,
                      const definition<crane::obj, T1> &d) {
    return definition<crane::obj, T1>{
        f(d.df_ty),
        tfmap<T1, crane::obj, crane::obj>(std::move(h), f, d.df_body)};
  }

  template <typename T1, typename F2>
  static modul<crane::obj, T1>
  TFunctor_mcfg(std::type_identity_t<TFunctor<T1>>,
                std::type_identity_t<TFunctor<definition<crane::obj, T1>>> h0,
                F2 &&f, const modul<crane::obj, T1> &p) {
    return modul<crane::obj, T1>{
        tfmap<List<definition<crane::obj, T1>>, crane::obj, crane::obj>(
            [=]() {
              return [=](crane::fn<crane::obj(crane::obj)> _x0,
                         const auto &_x1) -> List<definition<crane::obj, T1>> {
                return TFunctor_list_<definition<crane::obj, T1>>(
                    h0, _x0,
                    crane_convert<List<definition<crane::obj, T1>>>(_x1));
              };
            }(),
            f, p.m_defs)};
  }
  template <template <typename> class f>
  using ConvertTyp = crane::fn<f<Nat>(Nat, f<Nat>)>;

  template <template <typename> class T1>
  static T1<Nat> convert_typ(std::type_identity_t<ConvertTyp<T1>> convertTyp,
                             const Nat &x0_, T1<Nat> x1_) {
    return crane_container_cast<T1<Nat>>(convertTyp(x0_, std::move(x1_)));
  }

  static inline const ConvertTyp<mcfg> ConvertTyp_mcfg = []() {
    return [](Nat k, mcfg<Nat> eta0_) {
      return tfmap<modul<crane::obj, cfg<crane::obj>>, Nat, Nat>(
          []() {
            return [](crane::fn<crane::obj(crane::obj)> _x0,
                      const auto &_x1) -> modul<crane::obj, cfg<crane::obj>> {
              return TFunctor_mcfg<cfg<crane::obj>>(
                  [](auto &&_ec0, cfg<crane::obj> _ec1) {
                    return TFunctor_cfg(_ec0, _ec1);
                  },
                  []() {
                    return [](crane::fn<crane::obj(crane::obj)> _x0,
                              const auto &_x1)
                               -> definition<crane::obj, cfg<crane::obj>> {
                      return TFunctor_definition<cfg<crane::obj>>(
                          [](auto &&_ec0, cfg<crane::obj> _ec1) {
                            return TFunctor_cfg(_ec0, _ec1);
                          },
                          _x0,
                          crane_convert<
                              definition<crane::obj, cfg<crane::obj>>>(_x1));
                    };
                  }(),
                  _x0, crane_convert<modul<crane::obj, cfg<crane::obj>>>(_x1));
            };
          }(),
          [=](const Nat &n) { return n.add(k); }, eta0_);
    };
  }();
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
