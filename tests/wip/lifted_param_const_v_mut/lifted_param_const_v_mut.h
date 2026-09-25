#ifndef INCLUDED_LIFTED_PARAM_CONST_V_MUT
#define INCLUDED_LIFTED_PARAM_CONST_V_MUT

#include "crane_fn.h"
#include "small_vector.h"
#include <any>
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
using ptr = std::any;
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
    crane::small_vector<std::shared_ptr<Nat>> _stack = {};
    auto _drain = [&](variant_t &_v) {
      if (auto *_alt = std::get_if<S>(&_v)) {
        if (_alt->a0) {
          _stack.push_back(std::move(_alt->a0));
        }
      }
    };
    _drain(v_mut());
    while (!_stack.empty()) {
      auto _cur = std::move(_stack.back());
      _stack.pop_back();
      if (_cur.use_count() == 1) {
        std::atomic_thread_fence(std::memory_order_acquire);
        _drain(_cur->v_mut());
      }
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

  template <typename _U0, typename _U1> Sum(const Sum<_U0, _U1> &_other) {
    if (std::holds_alternative<typename Sum<_U0, _U1>::Inl>(_other.v())) {
      const auto &[a0] = std::get<typename Sum<_U0, _U1>::Inl>(_other.v());
      this->v_ = Inl{[&]() -> A {
        if constexpr (crane_convertible<A, const _U0 &>) {
          return crane_convert<A>(a0);
        } else {
          throw std::logic_error(
              "unreachable: inactive constructor field at this instantiation");
        }
      }()};
    } else {
      const auto &[a0] = std::get<typename Sum<_U0, _U1>::Inr>(_other.v());
      this->v_ = Inr{[&]() -> B {
        if constexpr (crane_convertible<B, const _U1 &>) {
          return crane_convert<B>(a0);
        } else {
          throw std::logic_error(
              "unreachable: inactive constructor field at this instantiation");
        }
      }()};
    }
  }

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

  template <typename _U> List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      this->v_ = Nil{};
    } else {
      const auto &[a, l] = std::get<typename List<_U>::Cons>(_other.v());
      this->v_ =
          Cons{[&]() -> A {
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
  }

  static List<A> nil() { return List<A>(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List<A>(Cons{std::move(a), std::make_shared<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  ~List() {
    crane::small_vector<std::shared_ptr<List<A>>> _stack = {};
    auto _drain = [&](variant_t &_v) {
      if (auto *_alt = std::get_if<Cons>(&_v)) {
        if (_alt->l) {
          _stack.push_back(std::move(_alt->l));
        }
      }
    };
    _drain(v_mut());
    while (!_stack.empty()) {
      auto _cur = std::move(_stack.back());
      _stack.pop_back();
      if (_cur.use_count() == 1) {
        std::atomic_thread_fence(std::memory_order_acquire);
        _drain(_cur->v_mut());
      }
    }
  }

  List(const List &) = default;
  List &operator=(const List &) = default;
  List(List &&) noexcept = default;
  List &operator=(List &&) noexcept = default;

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

  template <typename _U> Dvalue_base(const Dvalue_base<_U> &_other) {
    if (std::holds_alternative<typename Dvalue_base<_U>::DVALUE_Pointer>(
            _other.v())) {
      const auto &[a0] =
          std::get<typename Dvalue_base<_U>::DVALUE_Pointer>(_other.v());
      this->v_ = DVALUE_Pointer{a0};
    } else {
      const auto &[a0, a1] =
          std::get<typename Dvalue_base<_U>::DVALUE_I>(_other.v());
      this->v_ = DVALUE_I{a0, a1};
    }
  }

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

  template <typename _U> Dvalue(const Dvalue<_U> &_other) {
    if (std::holds_alternative<typename Dvalue<_U>::DVALUE_Base>(_other.v())) {
      const auto &[a0] = std::get<typename Dvalue<_U>::DVALUE_Base>(_other.v());
      this->v_ = DVALUE_Base{a0};
    } else {
      const auto &[a0] =
          std::get<typename Dvalue<_U>::DVALUE_Struct>(_other.v());
      this->v_ = DVALUE_Struct{a0};
    }
  }

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
auto _den_body(const T1 tag, const Dvalue<typename _tcI0::ptr> u) {
  if (std::holds_alternative<typename Dvalue<typename _tcI0::ptr>::DVALUE_Base>(
          u.v_mut())) {
    auto &[a0] =
        std::get<typename Dvalue<typename _tcI0::ptr>::DVALUE_Base>(u.v_mut());
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
    auto &[a00, a10] =
        std::get<typename List<Dvalue<typename _tcI0::ptr>>::Cons>(x0_.v_mut());
    const List<Dvalue<typename _tcI0::ptr>> &a10_value = *a10;
    if (std::holds_alternative<typename List<Dvalue<typename _tcI0::ptr>>::Nil>(
            a10_value.v())) {
      return Datatypes::template option_map<
          std::pair<Nat, Dvalue<typename _tcI0::ptr>>,
          Sum<Nat, Dvalue<typename _tcI0::ptr>>>(
          [](const std::pair<Nat, Dvalue<typename _tcI0::ptr>> &p) {
            return Sum<Nat, Dvalue<typename _tcI0::ptr>>::inr(p.second);
          },
          _den_body<_tcI0>(Nat::o(), std::move(a00)));
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
