#ifndef INCLUDED_LIFTED_PARAM_CONST_V_MUT
#define INCLUDED_LIFTED_PARAM_CONST_V_MUT

#include "crane_fn.h"
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
template <typename A, typename B> struct Sum;
template <typename A> struct List;
template <typename ptr> struct Dvalue_base;
template <typename ptr> struct Dvalue;
struct natParams;
using ptr = crane::obj;
template <typename
I>concept Params = requires {
    typename I::ptr;
    typename I::iptr;
  } && (requires {
    { I::nullp() } -> std::convertible_to<typename I::ptr>;
  } || requires {
    { I::nullp } -> std::convertible_to<typename I::ptr>;
  }) && (requires {
    { I::zeroi() } -> std::convertible_to<typename I::iptr>;
  } || requires {
    { I::zeroi } -> std::convertible_to<typename I::iptr>;
  });

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

template <typename A, typename B> struct Sum {
  // TYPES
  struct Inl {
    A a0;
  };

  struct Inr {
    B a0;
  };

  using variant_t = std::variant<Inl, Inr>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Sum() {}

  explicit Sum(Inl _v) : v_(std::move(_v)) {}

  explicit Sum(Inr _v) : v_(std::move(_v)) {}

  template <typename CraneU0, typename CraneU1>
  Sum(const Sum<CraneU0, CraneU1> &_other)
      : v_([&]() -> variant_t {
          if (std::holds_alternative<typename Sum<CraneU0, CraneU1>::Inl>(
                  _other.v())) {
            const auto &[a0] =
                std::get<typename Sum<CraneU0, CraneU1>::Inl>(_other.v());
            return Inl{[&]() -> A {
              if constexpr (crane_convertible<A, const CraneU0 &>) {
                return crane_convert<A>(a0);
              } else {
                throw std::logic_error("unreachable: inactive constructor "
                                       "field at this instantiation");
              }
            }()};
          } else {
            const auto &[a0] =
                std::get<typename Sum<CraneU0, CraneU1>::Inr>(_other.v());
            return Inr{[&]() -> B {
              if constexpr (crane_convertible<B, const CraneU1 &>) {
                return crane_convert<B>(a0);
              } else {
                throw std::logic_error("unreachable: inactive constructor "
                                       "field at this instantiation");
              }
            }()};
          }
        }()) {}

  static Sum<A, B> inl(A a0) { return Sum<A, B>(Inl{std::move(a0)}); }

  static Sum<A, B> inr(B a0) { return Sum<A, B>(Inr{std::move(a0)}); }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
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

struct Datatypes {
  template <typename T1, typename T2, typename F0>
    requires std::is_invocable_r_v<T2, F0 &, T1 &>
  static std::optional<T2> option_map(F0 &&f, const std::optional<T1> &o);
};

template <typename ptr> struct Dvalue_base {
  // TYPES
  struct DVALUE_Pointer {
    ptr a0;
  };

  struct DVALUE_I {
    Nat a0;
    Nat a1;
  };

  using variant_t = std::variant<DVALUE_Pointer, DVALUE_I>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Dvalue_base() {}

  explicit Dvalue_base(DVALUE_Pointer _v) : v_(std::move(_v)) {}

  explicit Dvalue_base(DVALUE_I _v) : v_(std::move(_v)) {}

  template <typename CraneU>
  Dvalue_base(const Dvalue_base<CraneU> &_other)
      : v_([&]() -> variant_t {
          if (std::holds_alternative<
                  typename Dvalue_base<CraneU>::DVALUE_Pointer>(_other.v())) {
            const auto &[a0] =
                std::get<typename Dvalue_base<CraneU>::DVALUE_Pointer>(
                    _other.v());
            return DVALUE_Pointer{[&]() -> ptr {
              if constexpr (crane_convertible<ptr, const CraneU &>) {
                return crane_convert<ptr>(a0);
              } else {
                throw std::logic_error("unreachable: inactive constructor "
                                       "field at this instantiation");
              }
            }()};
          } else {
            const auto &[a0, a1] =
                std::get<typename Dvalue_base<CraneU>::DVALUE_I>(_other.v());
            return DVALUE_I{a0, a1};
          }
        }()) {}

  static Dvalue_base<ptr> dvalue_pointer(ptr a0) {
    return Dvalue_base<ptr>(DVALUE_Pointer{std::move(a0)});
  }

  static Dvalue_base<ptr> dvalue_i(Nat a0, Nat a1) {
    return Dvalue_base<ptr>(DVALUE_I{std::move(a0), std::move(a1)});
  }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

template <typename ptr> struct Dvalue {
  // TYPES
  struct DVALUE_Base {
    Dvalue_base<ptr> a0;
  };

  struct DVALUE_Struct {
    std::shared_ptr<List<Dvalue<ptr>>> a0;
  };

  using variant_t = std::variant<DVALUE_Base, DVALUE_Struct>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Dvalue() {}

  explicit Dvalue(DVALUE_Base _v) : v_(std::move(_v)) {}

  explicit Dvalue(DVALUE_Struct _v) : v_(std::move(_v)) {}

  template <typename CraneU>
  Dvalue(const Dvalue<CraneU> &_other)
      : v_([&]() -> variant_t {
          if (std::holds_alternative<typename Dvalue<CraneU>::DVALUE_Base>(
                  _other.v())) {
            const auto &[a0] =
                std::get<typename Dvalue<CraneU>::DVALUE_Base>(_other.v());
            return DVALUE_Base{crane_convert<Dvalue_base<ptr>>(a0)};
          } else {
            const auto &[a0] =
                std::get<typename Dvalue<CraneU>::DVALUE_Struct>(_other.v());
            return DVALUE_Struct{
                (a0 ? std::make_shared<List<Dvalue<ptr>>>(
                          crane_convert<List<Dvalue<ptr>>>(*a0))
                    : nullptr)};
          }
        }()) {}

  static Dvalue<ptr> dvalue_base(Dvalue_base<ptr> a0) {
    return Dvalue<ptr>(DVALUE_Base{std::move(a0)});
  }

  static Dvalue<ptr> dvalue_struct(List<Dvalue<ptr>> a0);

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  template <Params _tcI0> Nat show_dvalue() const;
};

template <Params _tcI0, typename T1>
std::optional<std::pair<T1, Dvalue<typename _tcI0::ptr>>>
den_crane_body(const T1 tag, const Dvalue<typename _tcI0::ptr> u) {
  if (std::holds_alternative<typename Dvalue<typename _tcI0::ptr>::DVALUE_Base>(
          u.v())) {
    const auto &[a0] =
        std::get<typename Dvalue<typename _tcI0::ptr>::DVALUE_Base>(u.v());
    if (std::holds_alternative<
            typename Dvalue_base<typename _tcI0::ptr>::DVALUE_Pointer>(
            a0.v())) {
      if (u.template show_dvalue<_tcI0>().eqb(Nat::o())) {
        return std::optional<std::pair<T1, Dvalue<typename _tcI0::ptr>>>();
      } else {
        return std::make_optional<std::pair<T1, Dvalue<typename _tcI0::ptr>>>(
            std::make_pair(tag, u));
      }
    } else {
      const auto &[a00, a10] =
          std::get<typename Dvalue_base<typename _tcI0::ptr>::DVALUE_I>(a0.v());
      if (a00.eqb(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(
              Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(
                  Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(
                      Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(
                          Nat::s(Nat::o())))))))))))))))))))))))))))))))))) {
        return std::make_optional<std::pair<T1, Dvalue<typename _tcI0::ptr>>>(
            std::make_pair(
                tag, Dvalue<typename _tcI0::ptr>::dvalue_base(
                         Dvalue_base<typename _tcI0::ptr>::dvalue_i(
                             Nat::s(Nat::s(Nat::s(Nat::s(
                                 Nat::s(Nat::s(Nat::s(Nat::s(Nat::o())))))))),
                             a10))));
      } else {
        return std::optional<std::pair<T1, Dvalue<typename _tcI0::ptr>>>();
      }
    }
  } else {
    if (u.template show_dvalue<_tcI0>().eqb(Nat::o())) {
      return std::optional<std::pair<T1, Dvalue<typename _tcI0::ptr>>>();
    } else {
      return std::make_optional<std::pair<T1, Dvalue<typename _tcI0::ptr>>>(
          std::make_pair(tag, u));
    }
  }
}

template <Params _tcI0>
std::optional<Sum<Nat, Dvalue<typename _tcI0::ptr>>>
den(List<Dvalue<typename _tcI0::ptr>> x0_) {
  if (std::holds_alternative<typename List<Dvalue<typename _tcI0::ptr>>::Nil>(
          x0_.v_mut())) {
    return std::optional<Sum<Nat, Dvalue<typename _tcI0::ptr>>>();
  } else {
    auto &[a0, a1] =
        std::get<typename List<Dvalue<typename _tcI0::ptr>>::Cons>(x0_.v_mut());
    const List<Dvalue<typename _tcI0::ptr>> &a1_value = *a1;
    if (std::holds_alternative<typename List<Dvalue<typename _tcI0::ptr>>::Nil>(
            a1_value.v())) {
      return Datatypes::template option_map<
          std::pair<Nat, Dvalue<typename _tcI0::ptr>>,
          Sum<Nat, Dvalue<typename _tcI0::ptr>>>(
          [](const std::pair<Nat, Dvalue<typename _tcI0::ptr>> &p) {
            return Sum<Nat, Dvalue<typename _tcI0::ptr>>::inr(p.second);
          },
          den_crane_body<_tcI0>(Nat::o(), std::move(a0)));
    } else {
      return std::optional<Sum<Nat, Dvalue<typename _tcI0::ptr>>>();
    }
  }
}

struct natParams {
  using ptr = Nat;
  using iptr = Nat;

  static Nat nullp() { return Nat::o(); }

  static Nat zeroi() { return Nat::o(); }
};

static_assert(Params<natParams>);

struct LiftedParamConstVMut {
  static inline const std::optional<Sum<Nat, Dvalue<typename natParams::ptr>>>
      run = den<natParams>(List<Dvalue<Nat>>::cons(
          Dvalue<Nat>::dvalue_base(Dvalue_base<Nat>::dvalue_i(
              Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(
                  Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(
                      Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(
                          Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(
                              Nat::s(Nat::o())))))))))))))))))))))))))))))))),
              Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::o()))))))),
          List<Dvalue<Nat>>::nil()));
};

template <typename T1, typename T2, typename F0>
  requires std::is_invocable_r_v<T2, F0 &, T1 &>
std::optional<T2> Datatypes::option_map(F0 &&f, const std::optional<T1> &o) {
  if (o.has_value()) {
    const T1 &a = *o;
    return std::make_optional<T2>(f(a));
  } else {
    return std::optional<T2>();
  }
}

template <typename ptr>
Dvalue<ptr> Dvalue<ptr>::dvalue_struct(List<Dvalue<ptr>> a0) {
  return Dvalue<ptr>(
      DVALUE_Struct{std::make_shared<List<Dvalue<ptr>>>(std::move(a0))});
}

template <typename ptr>
template <Params _tcI0>
Nat Dvalue<ptr>::show_dvalue() const {
  if (std::holds_alternative<typename Dvalue<ptr>::DVALUE_Base>(this->v())) {
    return Nat::o();
  } else {
    return Nat::s(Nat::o());
  }
}

#endif // INCLUDED_LIFTED_PARAM_CONST_V_MUT
