#ifndef INCLUDED_FUNCTOR_RECORD_PROJ_AS_STATIC
#define INCLUDED_FUNCTOR_RECORD_PROJ_AS_STATIC

#include "crane_fn.h"
#include "small_vector.h"
#include <any>
#include <atomic>
#include <concepts>
#include <functional>
#include <memory>
#include <optional>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

struct Nat;
template <typename A> struct List;
enum class Comparison;
struct Positive;
struct Z;
template <typename X> struct Compare;

struct Datatypes {
  static Comparison CompOpp(Comparison r);
};

struct Coq_Pos {
  static bool eq_dec(const Positive &p, const Positive &x0);
};

struct Pos {
  static Positive succ(const Positive &x);
  static Positive add(const Positive &x, const Positive &y);
  static Positive add_carry(const Positive &x, const Positive &y);
  static Positive pred_double(const Positive &x);
  static Positive mul(const Positive &x, Positive y);
  static Comparison compare_cont(Comparison r, const Positive &x,
                                 const Positive &y);
  static Comparison compare(const Positive &x0_, const Positive &x1_);
  static bool eqb(const Positive &p, const Positive &q);
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

  Nat add0(Nat m) const {
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

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, A &, T1 &>
  T1 fold_right(F0 &&f, T1 a0) const {
    const List<A> *_self = this;

    /// _Enter: captures varying parameters for each recursive call.
    struct _Enter {
      const List<A> *_self;
    };

    /// _Resume_Cons: saves [a1], resumes after recursive call with _result.
    struct _Resume_Cons {
      std::decay_t<A> a1;
    };

    using _Frame = std::variant<_Enter, _Resume_Cons>;
    T1 _result{};
    crane::small_vector<_Frame> _stack;
    _stack.emplace_back(_Enter{_self});
    /// Loopified fold_right: _Enter -> _Resume_Cons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const List<A> *_self = _f._self;
        auto &&_sv = *_self;
        if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
          _result = a0;
        } else {
          const auto &[a1, a2] = std::get<typename List<A>::Cons>(_sv.v());
          _stack.emplace_back(_Resume_Cons{a1});
          _stack.emplace_back(_Enter{crane_raw(a2)});
        }
      } else {
        auto _f = std::move(std::get<_Resume_Cons>(_frame));
        _result = f(std::move(_f.a1), std::move(_result));
      }
    }
    return _result;
  }

  List<A> app(List<A> m) const {
    std::shared_ptr<List<A>> _head{};
    std::shared_ptr<List<A>> *_write = &_head;
    const List<A> *_loop_self = this;
    List<A> _loop_m = std::move(m);
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
        *_write = std::make_shared<List<A>>(std::move(_loop_m));
        break;
      } else {
        const auto &[a0, a1] = std::get<typename List<A>::Cons>(_sv.v());
        auto _cell =
            std::make_shared<List<A>>(typename List<A>::Cons(a0, nullptr));
        *_write = std::move(_cell);
        _write = &std::get<typename List<A>::Cons>((*_write)->v_mut()).l;
        _loop_self = crane_raw(a1);
        continue;
      }
    }
    return std::move(*_head);
  }
};
enum class Comparison { EQ, LT, GT };
template <typename M>
concept EqLtLe = requires { typename M::t; };

template <EqLtLe O, typename P> struct MakeOrderTac {};

struct Positive {
  // TYPES
  struct XI {
    std::shared_ptr<Positive> a0;
  };

  struct XO {
    std::shared_ptr<Positive> a0;
  };

  struct XH {};

  using variant_t = std::variant<XI, XO, XH>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Positive() {}

  explicit Positive(XI _v) : v_(std::move(_v)) {}

  explicit Positive(XO _v) : v_(std::move(_v)) {}

  explicit Positive(XH _v) : v_(_v) {}

  static Positive xi(Positive a0) {
    return Positive(XI{std::make_shared<Positive>(std::move(a0))});
  }

  static Positive xo(Positive a0) {
    return Positive(XO{std::make_shared<Positive>(std::move(a0))});
  }

  static Positive xh() { return Positive(XH{}); }

  // MANIPULATORS
  ~Positive() {
    crane::small_vector<std::shared_ptr<Positive>> _stack = {};
    auto _drain = [&](variant_t &_v) {
      if (auto *_alt = std::get_if<XI>(&_v)) {
        if (_alt->a0) {
          _stack.push_back(std::move(_alt->a0));
        }
      }
      if (auto *_alt = std::get_if<XO>(&_v)) {
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

  Positive(const Positive &) = default;
  Positive &operator=(const Positive &) = default;
  Positive(Positive &&) noexcept = default;
  Positive &operator=(Positive &&) noexcept = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct Z {
  // TYPES
  struct Z0 {};

  struct Zpos {
    Positive a0;
  };

  struct Zneg {
    Positive a0;
  };

  using variant_t = std::variant<Z0, Zpos, Zneg>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Z() {}

  explicit Z(Z0 _v) : v_(_v) {}

  explicit Z(Zpos _v) : v_(std::move(_v)) {}

  explicit Z(Zneg _v) : v_(std::move(_v)) {}

  static Z z0() { return Z(Z0{}); }

  static Z zpos(Positive a0) { return Z(Zpos{std::move(a0)}); }

  static Z zneg(Positive a0) { return Z(Zneg{std::move(a0)}); }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

template <typename X> struct Compare {
  // TYPES
  struct LT {};

  struct EQ {};

  struct GT {};

  using variant_t = std::variant<LT, EQ, GT>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Compare() {}

  explicit Compare(LT _v) : v_(_v) {}

  explicit Compare(EQ _v) : v_(_v) {}

  explicit Compare(GT _v) : v_(_v) {}

  static Compare<X> lt() { return Compare<X>(LT{}); }

  static Compare<X> eq() { return Compare<X>(EQ{}); }

  static Compare<X> gt() { return Compare<X>(GT{}); }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

template <typename M>
concept OrderedType = requires {
  typename M::t;
  {
    M::compare(std::declval<typename M::t>(), std::declval<typename M::t>())
  } -> std::same_as<Compare<typename M::t>>;
  {
    M::eq_dec(std::declval<typename M::t>(), std::declval<typename M::t>())
  } -> std::same_as<bool>;
};

template <OrderedType O> struct OrderedTypeFacts {
  struct TO {
    using t = typename O::t;
  };

  struct IsTO {};

  using OrderTac = MakeOrderTac<TO, IsTO>;

  static bool eq_dec(typename O::t x0_, typename O::t x1_) {
    return O::eq_dec(std::move(x0_), std::move(x1_));
  }

  static bool lt_dec(typename O::t x, typename O::t y) {
    auto &&_sv = O::compare(x, y);
    if (std::holds_alternative<typename Compare<typename O::t>::LT>(_sv.v())) {
      return true;
    } else {
      return false;
    }
  }

  static bool eqb(typename O::t x, typename O::t y) {
    if (eq_dec(x, y)) {
      return true;
    } else {
      return false;
    }
  }
};

template <OrderedType O> struct KeyOrderedType {
  using MO = OrderedTypeFacts<O>;
};

template <OrderedType X> struct Coq_Raw {
  using MX = OrderedTypeFacts<X>;
  using PX = KeyOrderedType<X>;
  using key = typename X::t;
  template <typename elt> using t = List<std::pair<typename X::t, elt>>;

  template <typename T1> static const t<T1> &empty() {
    static const t<T1> v = List<std::pair<typename X::t, T1>>::nil();
    return v;
  }

  template <typename T1>
  static bool is_empty(const List<std::pair<typename X::t, T1>> &l) {
    if (std::holds_alternative<
            typename List<std::pair<typename X::t, T1>>::Nil>(l.v())) {
      return true;
    } else {
      return false;
    }
  }

  template <typename T1>
  static bool mem(typename X::t k,
                  const List<std::pair<typename X::t, T1>> &s) {
    if (std::holds_alternative<
            typename List<std::pair<typename X::t, T1>>::Nil>(s.v())) {
      return false;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<std::pair<typename X::t, T1>>::Cons>(s.v());
      const auto &[k_, _x] = a0;
      auto &&_sv = X::compare(k, k_);
      if (std::holds_alternative<typename Compare<typename X::t>::LT>(
              _sv.v())) {
        return false;
      } else if (std::holds_alternative<typename Compare<typename X::t>::EQ>(
                     _sv.v())) {
        return true;
      } else {
        return mem<T1>(k, *a1);
      }
    }
  }

  template <typename T1>
  static std::optional<T1> find(typename X::t k,
                                const List<std::pair<typename X::t, T1>> &s) {
    if (std::holds_alternative<
            typename List<std::pair<typename X::t, T1>>::Nil>(s.v())) {
      return std::optional<T1>();
    } else {
      const auto &[a0, a1] =
          std::get<typename List<std::pair<typename X::t, T1>>::Cons>(s.v());
      const auto &[k_, x] = a0;
      auto &&_sv = X::compare(k, k_);
      if (std::holds_alternative<typename Compare<typename X::t>::LT>(
              _sv.v())) {
        return std::optional<T1>();
      } else if (std::holds_alternative<typename Compare<typename X::t>::EQ>(
                     _sv.v())) {
        return std::make_optional<T1>(x);
      } else {
        return find<T1>(k, *a1);
      }
    }
  }

  template <typename T1>
  static t<T1> add(typename X::t k, T1 x,
                   List<std::pair<typename X::t, T1>> s) {
    if (std::holds_alternative<
            typename List<std::pair<typename X::t, T1>>::Nil>(s.v_mut())) {
      return List<std::pair<typename X::t, T1>>::cons(
          std::make_pair(k, x), List<std::pair<typename X::t, T1>>::nil());
    } else {
      auto &[a0, a1] =
          std::get<typename List<std::pair<typename X::t, T1>>::Cons>(
              s.v_mut());
      const auto &[k_, y] = a0;
      auto &&_sv = X::compare(k, k_);
      if (std::holds_alternative<typename Compare<typename X::t>::LT>(
              _sv.v())) {
        return List<std::pair<typename X::t, T1>>::cons(std::make_pair(k, x),
                                                        s);
      } else if (std::holds_alternative<typename Compare<typename X::t>::EQ>(
                     _sv.v())) {
        return List<std::pair<typename X::t, T1>>::cons(std::make_pair(k, x),
                                                        *a1);
      } else {
        return List<std::pair<typename X::t, T1>>::cons(std::make_pair(k_, y),
                                                        add<T1>(k, x, *a1));
      }
    }
  }

  template <typename T1>
  static t<T1> remove(typename X::t k, List<std::pair<typename X::t, T1>> s) {
    if (std::holds_alternative<
            typename List<std::pair<typename X::t, T1>>::Nil>(s.v_mut())) {
      return List<std::pair<typename X::t, T1>>::nil();
    } else {
      auto &[a0, a1] =
          std::get<typename List<std::pair<typename X::t, T1>>::Cons>(
              s.v_mut());
      const auto &[k_, x] = a0;
      auto &&_sv = X::compare(k, k_);
      if (std::holds_alternative<typename Compare<typename X::t>::LT>(
              _sv.v())) {
        return s;
      } else if (std::holds_alternative<typename Compare<typename X::t>::EQ>(
                     _sv.v())) {
        return *a1;
      } else {
        return List<std::pair<typename X::t, T1>>::cons(std::make_pair(k_, x),
                                                        remove<T1>(k, *a1));
      }
    }
  }

  template <typename T1>
  static t<T1> elements(List<std::pair<typename X::t, T1>> m) {
    return m;
  }

  template <typename T1, typename T2, typename F0>
    requires std::is_invocable_r_v<T2, F0 &, typename X::t &, T1 &, T2 &>
  static T2 fold(F0 &&f, const List<std::pair<typename X::t, T1>> &m, T2 acc) {
    if (std::holds_alternative<
            typename List<std::pair<typename X::t, T1>>::Nil>(m.v())) {
      return acc;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<std::pair<typename X::t, T1>>::Cons>(m.v());
      const auto &[k, e] = a0;
      return fold<T1, T2>(f, *a1, f(k, e, std::move(acc)));
    }
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<bool, F0 &, T1 &, T1 &>
  static bool equal(F0 &&cmp, const List<std::pair<typename X::t, T1>> &m,
                    const List<std::pair<typename X::t, T1>> &m_) {
    if (std::holds_alternative<
            typename List<std::pair<typename X::t, T1>>::Nil>(m.v())) {
      if (std::holds_alternative<
              typename List<std::pair<typename X::t, T1>>::Nil>(m_.v())) {
        return true;
      } else {
        return false;
      }
    } else {
      const auto &[a0, a1] =
          std::get<typename List<std::pair<typename X::t, T1>>::Cons>(m.v());
      const auto &[x, e] = a0;
      if (std::holds_alternative<
              typename List<std::pair<typename X::t, T1>>::Nil>(m_.v())) {
        return false;
      } else {
        const auto &[a00, a10] =
            std::get<typename List<std::pair<typename X::t, T1>>::Cons>(m_.v());
        const auto &[x_, e_] = a00;
        auto &&_sv = X::compare(x, x_);
        if (std::holds_alternative<typename Compare<typename X::t>::EQ>(
                _sv.v())) {
          return (cmp(e, e_) && equal<T1>(cmp, *a1, *a10));
        } else {
          return false;
        }
      }
    }
  }

  template <typename T1, typename T2, typename F0>
    requires std::is_invocable_r_v<T2, F0 &, T1 &>
  static t<T2> map(F0 &&f, const List<std::pair<typename X::t, T1>> &m) {
    if (std::holds_alternative<
            typename List<std::pair<typename X::t, T1>>::Nil>(m.v())) {
      return List<std::pair<typename X::t, T2>>::nil();
    } else {
      const auto &[a0, a1] =
          std::get<typename List<std::pair<typename X::t, T1>>::Cons>(m.v());
      const auto &[k, e] = a0;
      return List<std::pair<typename X::t, T2>>::cons(std::make_pair(k, f(e)),
                                                      map<T1, T2>(f, *a1));
    }
  }

  template <typename T1, typename T2, typename F0>
    requires std::is_invocable_r_v<T2, F0 &, typename X::t &, T1 &>
  static t<T2> mapi(F0 &&f, const List<std::pair<typename X::t, T1>> &m) {
    if (std::holds_alternative<
            typename List<std::pair<typename X::t, T1>>::Nil>(m.v())) {
      return List<std::pair<typename X::t, T2>>::nil();
    } else {
      const auto &[a0, a1] =
          std::get<typename List<std::pair<typename X::t, T1>>::Cons>(m.v());
      const auto &[k, e] = a0;
      return List<std::pair<typename X::t, T2>>::cons(
          std::make_pair(k, f(k, e)), mapi<T1, T2>(f, *a1));
    }
  }

  template <typename T1>
  static List<std::pair<key, T1>>
  option_cons(typename X::t k, const std::optional<T1> &o,
              List<std::pair<typename X::t, T1>> l) {
    if (o.has_value()) {
      const T1 &e = *o;
      return List<std::pair<key, T1>>::cons(std::make_pair(k, e), std::move(l));
    } else {
      return l;
    }
  }

  template <typename T1, typename T2, typename T3, typename F0>
    requires std::is_invocable_r_v<std::optional<T3>, F0 &, std::optional<T1> &,
                                   std::optional<T2> &>
  static t<T3> map2_l(F0 &&f, const List<std::pair<typename X::t, T1>> &m) {
    if (std::holds_alternative<
            typename List<std::pair<typename X::t, T1>>::Nil>(m.v())) {
      return List<std::pair<typename X::t, T3>>::nil();
    } else {
      const auto &[a0, a1] =
          std::get<typename List<std::pair<typename X::t, T1>>::Cons>(m.v());
      const auto &[k, e] = a0;
      return option_cons<T3>(k,
                             f(std::make_optional<T1>(e), std::optional<T2>()),
                             map2_l<T1, T2, T3>(f, *a1));
    }
  }

  template <typename T1, typename T2, typename T3, typename F0>
    requires std::is_invocable_r_v<std::optional<T3>, F0 &, std::optional<T1> &,
                                   std::optional<T2> &>
  static t<T3> map2_r(F0 &&f, const List<std::pair<typename X::t, T2>> &m_) {
    if (std::holds_alternative<
            typename List<std::pair<typename X::t, T2>>::Nil>(m_.v())) {
      return List<std::pair<typename X::t, T3>>::nil();
    } else {
      const auto &[a0, a1] =
          std::get<typename List<std::pair<typename X::t, T2>>::Cons>(m_.v());
      const auto &[k, e_] = a0;
      return option_cons<T3>(k,
                             f(std::optional<T1>(), std::make_optional<T2>(e_)),
                             map2_r<T1, T2, T3>(f, *a1));
    }
  }

  template <typename T1, typename T2, typename T3, typename F0>
    requires std::is_invocable_r_v<std::optional<T3>, F0 &, std::optional<T1> &,
                                   std::optional<T2> &>
  static t<T3> map2(F0 &&f, List<std::pair<typename X::t, T1>> m, t<T2> x0_) {
    return [=]() mutable -> std::function<List<std::pair<typename X::t, T3>>(
                             List<std::pair<typename X::t, T2>>)> {
      if (std::holds_alternative<
              typename List<std::pair<typename X::t, T1>>::Nil>(m.v_mut())) {
        return [=](t<T2> _x0) mutable -> t<T3> {
          return map2_r<T1, T2, T3>(f, _x0);
        };
      } else {
        auto &[a0, a1] =
            std::get<typename List<std::pair<typename X::t, T1>>::Cons>(
                m.v_mut());
        const List<std::pair<typename X::t, T1>> &a1_value = *a1;
        const auto &[k, e] = a0;
        auto map2_aux_impl = [=](auto &_self_map2_aux,
                                 List<std::pair<typename X::t, T2>> m_) mutable
            -> List<std::pair<typename X::t, T3>> {
          if (std::holds_alternative<
                  typename List<std::pair<typename X::t, T2>>::Nil>(m_.v())) {
            return map2_l<T1, T2, T3>(f, m);
          } else {
            const auto &[a00, a10] =
                std::get<typename List<std::pair<typename X::t, T2>>::Cons>(
                    m_.v());
            const auto &[k_, e_] = a00;
            auto &&_sv = X::compare(k, k_);
            if (std::holds_alternative<typename Compare<typename X::t>::LT>(
                    _sv.v())) {
              return option_cons<T3>(
                  k, f(std::make_optional<T1>(e), std::optional<T2>()),
                  map2<T1, T2, T3>(f, a1_value, m_));
            } else if (std::holds_alternative<
                           typename Compare<typename X::t>::EQ>(_sv.v())) {
              return option_cons<T3>(
                  k, f(std::make_optional<T1>(e), std::make_optional<T2>(e_)),
                  map2<T1, T2, T3>(f, a1_value, *a10));
            } else {
              return option_cons<T3>(
                  k_, f(std::optional<T1>(), std::make_optional<T2>(e_)),
                  _self_map2_aux(_self_map2_aux, *a10));
            }
          }
        };
        auto map2_aux = [=](List<std::pair<typename X::t, T2>> m_) mutable
            -> List<std::pair<typename X::t, T3>> {
          return map2_aux_impl(map2_aux_impl, m_);
        };
        return map2_aux;
      }
    }()(std::move(x0_));
  }

  template <typename T1, typename T2>
  static t<std::pair<std::optional<T1>, std::optional<T2>>>
  combine(const List<std::pair<typename X::t, T1>> &m, t<T2> x0_) {
    return [=]() mutable
               -> std::function<
                   List<std::pair<typename X::t, std::pair<std::optional<T1>,
                                                           std::optional<T2>>>>(
                       List<std::pair<typename X::t, T2>>)> {
      if (std::holds_alternative<
              typename List<std::pair<typename X::t, T1>>::Nil>(m.v())) {
        return [](t<T2> _x0)
                   -> t<std::pair<std::optional<T1>, std::optional<T2>>> {
          return map<T2, std::pair<std::optional<T1>, std::optional<T2>>>(
              [](T2 e_) {
                return std::make_pair(std::optional<T1>(),
                                      std::make_optional<T2>(e_));
              },
              _x0);
        };
      } else {
        const auto &[a0, a1] =
            std::get<typename List<std::pair<typename X::t, T1>>::Cons>(m.v());
        const List<std::pair<typename X::t, T1>> &a1_value = *a1;
        const auto &[k, e] = a0;
        auto combine_aux_impl =
            [=](auto &_self_combine_aux,
                List<std::pair<typename X::t, T2>> m_) mutable
            -> List<std::pair<typename X::t, std::pair<std::optional<T1>,
                                                       std::optional<T2>>>> {
          if (std::holds_alternative<
                  typename List<std::pair<typename X::t, T2>>::Nil>(m_.v())) {
            return map<T1, std::pair<std::optional<T1>, std::optional<T2>>>(
                [](T1 e0) {
                  return std::make_pair(std::make_optional<T1>(e0),
                                        std::optional<T2>());
                },
                m);
          } else {
            const auto &[a00, a10] =
                std::get<typename List<std::pair<typename X::t, T2>>::Cons>(
                    m_.v());
            const auto &[k_, e_] = a00;
            auto &&_sv = X::compare(k, k_);
            if (std::holds_alternative<typename Compare<typename X::t>::LT>(
                    _sv.v())) {
              return List<
                  std::pair<typename X::t,
                            std::pair<std::optional<T1>, std::optional<T2>>>>::
                  cons(std::make_pair(k,
                                      std::make_pair(std::make_optional<T1>(e),
                                                     std::optional<T2>())),
                       combine<T1, T2>(a1_value, m_));
            } else if (std::holds_alternative<
                           typename Compare<typename X::t>::EQ>(_sv.v())) {
              return List<
                  std::pair<typename X::t,
                            std::pair<std::optional<T1>, std::optional<T2>>>>::
                  cons(std::make_pair(
                           k, std::make_pair(std::make_optional<T1>(e),
                                             std::make_optional<T2>(e_))),
                       combine<T1, T2>(a1_value, *a10));
            } else {
              return List<
                  std::pair<typename X::t,
                            std::pair<std::optional<T1>, std::optional<T2>>>>::
                  cons(std::make_pair(
                           k_, std::make_pair(std::optional<T1>(),
                                              std::make_optional<T2>(e_))),
                       _self_combine_aux(_self_combine_aux, *a10));
            }
          }
        };
        auto combine_aux = [=](List<std::pair<typename X::t, T2>> m_) mutable
            -> List<std::pair<typename X::t, std::pair<std::optional<T1>,
                                                       std::optional<T2>>>> {
          return combine_aux_impl(combine_aux_impl, m_);
        };
        return combine_aux;
      }
    }()(std::move(x0_));
  }

  template <typename T1, typename T2, typename T3, typename F0>
    requires std::is_invocable_r_v<T3, F0 &, T1 &, T2 &, T3 &>
  static T3 fold_right_pair(F0 &&f, const List<std::pair<T1, T2>> &l,
                            const T3 &i) {
    return l.template fold_right<T3>(
        [=](const std::pair<T1, T2> &p) mutable {
          return [=](T3 _pa0) mutable { return f(p.first, p.second, _pa0); };
        },
        i);
  }

  template <typename T1, typename T2, typename T3, typename F0>
    requires std::is_invocable_r_v<std::optional<T3>, F0 &, std::optional<T1> &,
                                   std::optional<T2> &>
  static List<std::pair<key, T3>>
  map2_alt(F0 &&f, const List<std::pair<typename X::t, T1>> &m,
           const List<std::pair<typename X::t, T2>> &m_) {
    List<std::pair<typename X::t,
                   std::pair<std::optional<T1>, std::optional<T2>>>>
        m0 = combine<T1, T2>(m, m_);
    List<std::pair<typename X::t, std::optional<T3>>> m1 =
        map<std::pair<std::optional<T1>, std::optional<T2>>, std::optional<T3>>(
            [=](const std::pair<std::optional<T1>, std::optional<T2>>
                    &p) mutable { return f(p.first, p.second); },
            std::move(m0));
    return fold_right_pair<key, std::optional<T3>, List<std::pair<key, T3>>>(
        option_cons<T3>, std::move(m1), List<std::pair<key, T3>>::nil());
  }

  template <typename T1, typename T2>
  static std::optional<std::pair<std::optional<T1>, std::optional<T2>>>
  at_least_one(std::optional<T1> o, std::optional<T2> o_) {
    if (o.has_value()) {
      const T1 &_x = *o;
      return std::make_optional<
          std::pair<std::optional<T1>, std::optional<T2>>>(
          std::make_pair(std::move(o), std::move(o_)));
    } else {
      if (o_.has_value()) {
        const T2 &_x = *o_;
        return std::make_optional<
            std::pair<std::optional<T1>, std::optional<T2>>>(
            std::make_pair(std::move(o), std::move(o_)));
      } else {
        return std::optional<std::pair<std::optional<T1>, std::optional<T2>>>();
      }
    }
  }

  template <typename T1, typename T2, typename T3, typename F0>
    requires std::is_invocable_r_v<std::optional<T3>, F0 &, std::optional<T1> &,
                                   std::optional<T2> &>
  static std::optional<T3> at_least_one_then_f(F0 &&f,
                                               const std::optional<T1> &o,
                                               const std::optional<T2> &o_) {
    if (o.has_value()) {
      const T1 &_x = *o;
      return f(o, o_);
    } else {
      if (o_.has_value()) {
        const T2 &_x = *o_;
        return f(o, o_);
      } else {
        return std::optional<T3>();
      }
    }
  }
};

struct BinInt {
  static Z double_(const Z &x);
  static Z succ_double(const Z &x);
  static Z pred_double(const Z &x);
  static Z pos_sub(const Positive &x, const Positive &y);
  static Z add(Z x, Z y);
  static Z opp(const Z &x);
  static Z sub(const Z &m, const Z &n);
  static Z mul(const Z &x, const Z &y);
  static Comparison compare(const Z &x, const Z &y);
  static bool leb(const Z &x, const Z &y);
  static bool ltb(const Z &x, const Z &y);
  static bool eqb(const Z &x, const Z &y);
  static Z max(Z n, Z m);
  static bool eq_dec(const Z &x, const Z &y);
};

template <typename M>
concept Int = requires {
  typename M::t;
  { M::i2z(std::declval<typename M::t>()) } -> std::same_as<Z>;
  requires(
      requires {
        { M::_0 } -> std::convertible_to<typename M::t>;
      } ||
      requires {
        { M::_0() } -> std::convertible_to<typename M::t>;
      });
  requires(
      requires {
        { M::_1 } -> std::convertible_to<typename M::t>;
      } ||
      requires {
        { M::_1() } -> std::convertible_to<typename M::t>;
      });
  requires(
      requires {
        { M::_2 } -> std::convertible_to<typename M::t>;
      } ||
      requires {
        { M::_2() } -> std::convertible_to<typename M::t>;
      });
  requires(
      requires {
        { M::_3 } -> std::convertible_to<typename M::t>;
      } ||
      requires {
        { M::_3() } -> std::convertible_to<typename M::t>;
      });
  {
    M::add(std::declval<typename M::t>(), std::declval<typename M::t>())
  } -> std::same_as<typename M::t>;
  { M::opp(std::declval<typename M::t>()) } -> std::same_as<typename M::t>;
  {
    M::sub(std::declval<typename M::t>(), std::declval<typename M::t>())
  } -> std::same_as<typename M::t>;
  {
    M::mul(std::declval<typename M::t>(), std::declval<typename M::t>())
  } -> std::same_as<typename M::t>;
  {
    M::max(std::declval<typename M::t>(), std::declval<typename M::t>())
  } -> std::same_as<typename M::t>;
  {
    M::eqb(std::declval<typename M::t>(), std::declval<typename M::t>())
  } -> std::same_as<bool>;
  {
    M::ltb(std::declval<typename M::t>(), std::declval<typename M::t>())
  } -> std::same_as<bool>;
  {
    M::leb(std::declval<typename M::t>(), std::declval<typename M::t>())
  } -> std::same_as<bool>;
  {
    M::gt_le_dec(std::declval<typename M::t>(), std::declval<typename M::t>())
  } -> std::same_as<bool>;
  {
    M::ge_lt_dec(std::declval<typename M::t>(), std::declval<typename M::t>())
  } -> std::same_as<bool>;
  {
    M::eq_dec(std::declval<typename M::t>(), std::declval<typename M::t>())
  } -> std::same_as<bool>;
};

struct Z_as_Int {
  using t = Z;
  static inline const Z _0 = Z::z0();
  static inline const Z _1 = Z::zpos(Positive::xh());
  static inline const Z _2 = Z::zpos(Positive::xo(Positive::xh()));
  static inline const Z _3 = Z::zpos(Positive::xi(Positive::xh()));
  static Z add(const Z &x0_, const Z &x1_);
  static Z opp(const Z &x0_);
  static Z sub(const Z &x0_, const Z &x1_);
  static Z mul(const Z &x0_, const Z &x1_);
  static Z max(const Z &x0_, const Z &x1_);
  static bool eqb(const Z &x0_, const Z &x1_);
  static bool ltb(const Z &x0_, const Z &x1_);
  static bool leb(const Z &x0_, const Z &x1_);
  static bool eq_dec(const Z &x0_, const Z &x1_);
  static bool gt_le_dec(const Z &i, const Z &j);
  static bool ge_lt_dec(const Z &i, const Z &j);
  static Z i2z(Z n);
};

struct Z_as_OT {
  using t = Z;
  static Compare<Z> compare(const Z &x, const Z &y);
  static bool eq_dec(const Z &x0_, const Z &x1_);
};

template <Int I, OrderedType X> struct Raw {
  using key = typename X::t;

  template <typename elt> struct tree {
    // TYPES
    struct Leaf {};

    struct Node {
      std::shared_ptr<tree<elt>> a0;
      key a1;
      elt a2;
      std::shared_ptr<tree<elt>> a3;
      typename I::t a4;
    };

    using variant_t = std::variant<Leaf, Node>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    tree() {}

    explicit tree(Leaf _v) : v_(_v) {}

    explicit tree(Node _v) : v_(std::move(_v)) {}

    template <typename _U> tree(const tree<_U> &_other) {
      if (std::holds_alternative<typename tree<_U>::Leaf>(_other.v())) {
        this->v_ = Leaf{};
      } else {
        const auto &[a0, a1, a2, a3, a4] =
            std::get<typename tree<_U>::Node>(_other.v());
        this->v_ = Node{
            (a0 ? std::make_shared<tree<elt>>(crane_convert<tree<elt>>(*a0))
                : nullptr),
            a1,
            [&]() -> elt {
              if constexpr (crane_convertible<elt, const _U &>) {
                return crane_convert<elt>(a2);
              } else {
                throw std::logic_error("unreachable: inactive constructor "
                                       "field at this instantiation");
              }
            }(),
            (a3 ? std::make_shared<tree<elt>>(crane_convert<tree<elt>>(*a3))
                : nullptr),
            a4};
      }
    }

    static tree<elt> leaf() { return tree<elt>(Leaf{}); }

    static tree<elt> node(tree<elt> a0, key a1, elt a2, tree<elt> a3,
                          typename I::t a4) {
      return tree<elt>(Node{std::make_shared<tree<elt>>(std::move(a0)),
                            std::move(a1), std::move(a2),
                            std::make_shared<tree<elt>>(std::move(a3)),
                            std::move(a4)});
    }

    // MANIPULATORS
    ~tree() {
      crane::small_vector<std::shared_ptr<tree<elt>>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<Node>(&_v)) {
          if (_alt->a0) {
            _stack.push_back(std::move(_alt->a0));
          }
          if (_alt->a3) {
            _stack.push_back(std::move(_alt->a3));
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

    tree(const tree &) = default;
    tree &operator=(const tree &) = default;
    tree(tree &&) noexcept = default;
    tree &operator=(tree &&) noexcept = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename T2, typename F1>
    requires std::is_invocable_r_v<T2, F1 &, tree<T1> &, T2 &, typename X::t &,
                                   T1 &, tree<T1> &, T2 &, typename I::t &>
  static T2 tree_rect(T2 f, F1 &&f0, const tree<T1> &t0) {
    if (std::holds_alternative<typename tree<T1>::Leaf>(t0.v())) {
      return f;
    } else {
      const auto &[a0, a1, a2, a3, a4] =
          std::get<typename tree<T1>::Node>(t0.v());
      return f0(*a0, tree_rect<T1, T2>(f, f0, *a0), a1, a2, *a3,
                tree_rect<T1, T2>(f, f0, *a3), a4);
    }
  }

  template <typename T1, typename T2, typename F1>
    requires std::is_invocable_r_v<T2, F1 &, tree<T1> &, T2 &, typename X::t &,
                                   T1 &, tree<T1> &, T2 &, typename I::t &>
  static T2 tree_rec(T2 f, F1 &&f0, const tree<T1> &t0) {
    if (std::holds_alternative<typename tree<T1>::Leaf>(t0.v())) {
      return f;
    } else {
      const auto &[a0, a1, a2, a3, a4] =
          std::get<typename tree<T1>::Node>(t0.v());
      return f0(*a0, tree_rec<T1, T2>(f, f0, *a0), a1, a2, *a3,
                tree_rec<T1, T2>(f, f0, *a3), a4);
    }
  }

  template <typename T1> static typename I::t height(const tree<T1> &m) {
    if (std::holds_alternative<typename tree<T1>::Leaf>(m.v())) {
      return I::_0;
    } else {
      const auto &[a0, a1, a2, a3, a4] =
          std::get<typename tree<T1>::Node>(m.v());
      return a4;
    }
  }

  template <typename T1> static Nat cardinal(const tree<T1> &m) {
    if (std::holds_alternative<typename tree<T1>::Leaf>(m.v())) {
      return Nat::o();
    } else {
      const auto &[a0, a1, a2, a3, a4] =
          std::get<typename tree<T1>::Node>(m.v());
      return Nat::s(cardinal<T1>(*a0).add0(cardinal<T1>(*a3)));
    }
  }

  template <typename T1> static const tree<T1> &empty() {
    static const tree<T1> v = tree<T1>::leaf();
    return v;
  }

  template <typename T1> static bool is_empty(const tree<T1> &m) {
    if (std::holds_alternative<typename tree<T1>::Leaf>(m.v())) {
      return true;
    } else {
      return false;
    }
  }

  template <typename T1> static bool mem(typename X::t x, const tree<T1> &m) {
    if (std::holds_alternative<typename tree<T1>::Leaf>(m.v())) {
      return false;
    } else {
      const auto &[a0, a1, a2, a3, a4] =
          std::get<typename tree<T1>::Node>(m.v());
      auto &&_sv = X::compare(x, a1);
      if (std::holds_alternative<typename Compare<typename X::t>::LT>(
              _sv.v())) {
        return mem<T1>(x, *a0);
      } else if (std::holds_alternative<typename Compare<typename X::t>::EQ>(
                     _sv.v())) {
        return true;
      } else {
        return mem<T1>(x, *a3);
      }
    }
  }

  template <typename T1>
  static std::optional<T1> find(typename X::t x, const tree<T1> &m) {
    if (std::holds_alternative<typename tree<T1>::Leaf>(m.v())) {
      return std::optional<T1>();
    } else {
      const auto &[a0, a1, a2, a3, a4] =
          std::get<typename tree<T1>::Node>(m.v());
      auto &&_sv = X::compare(x, a1);
      if (std::holds_alternative<typename Compare<typename X::t>::LT>(
              _sv.v())) {
        return find<T1>(x, *a0);
      } else if (std::holds_alternative<typename Compare<typename X::t>::EQ>(
                     _sv.v())) {
        return std::make_optional<T1>(a2);
      } else {
        return find<T1>(x, *a3);
      }
    }
  }

  template <typename T1>
  static tree<T1> create(tree<T1> l, typename X::t x, T1 e, tree<T1> r) {
    return tree<T1>::node(l, std::move(x), std::move(e), r,
                          I::add(I::max(height<T1>(l), height<T1>(r)), I::_1));
  }

  template <typename T1>
  static tree<T1> assert_false(const tree<T1> &x0_, key x1_, const T1 &x2_,
                               const tree<T1> &x3_) {
    return create<T1>(x0_, std::move(x1_), x2_, x3_);
  }

  template <typename T1>
  static tree<T1> bal(const tree<T1> &l, typename X::t x, const T1 &d,
                      const tree<T1> &r) {
    typename I::t hl = height<T1>(l);
    typename I::t hr = height<T1>(r);
    if (I::gt_le_dec(hl, I::add(hr, I::_2))) {
      if (std::holds_alternative<typename tree<T1>::Leaf>(l.v())) {
        return assert_false<T1>(l, std::move(x), d, r);
      } else {
        const auto &[a0, a1, a2, a3, a4] =
            std::get<typename tree<T1>::Node>(l.v());
        if (I::ge_lt_dec(height<T1>(*a0), height<T1>(*a3))) {
          return create<T1>(*a0, a1, a2, create<T1>(*a3, std::move(x), d, r));
        } else {
          auto &&_sv0 = *a3;
          if (std::holds_alternative<typename tree<T1>::Leaf>(_sv0.v())) {
            return assert_false<T1>(l, std::move(x), d, r);
          } else {
            const auto &[a00, a10, a20, a30, a40] =
                std::get<typename tree<T1>::Node>(_sv0.v());
            return create<T1>(create<T1>(*a0, a1, a2, *a00), a10, a20,
                              create<T1>(*a30, std::move(x), d, r));
          }
        }
      }
    } else {
      if (I::gt_le_dec(hr, I::add(hl, I::_2))) {
        if (std::holds_alternative<typename tree<T1>::Leaf>(r.v())) {
          return assert_false<T1>(l, std::move(x), d, r);
        } else {
          const auto &[a00, a10, a20, a30, a40] =
              std::get<typename tree<T1>::Node>(r.v());
          if (I::ge_lt_dec(height<T1>(*a30), height<T1>(*a00))) {
            return create<T1>(create<T1>(l, std::move(x), d, *a00), a10, a20,
                              *a30);
          } else {
            auto &&_sv1 = *a00;
            if (std::holds_alternative<typename tree<T1>::Leaf>(_sv1.v())) {
              return assert_false<T1>(l, std::move(x), d, r);
            } else {
              const auto &[a01, a11, a21, a31, a41] =
                  std::get<typename tree<T1>::Node>(_sv1.v());
              return create<T1>(create<T1>(l, std::move(x), d, *a01), a11, a21,
                                create<T1>(*a31, a10, a20, *a30));
            }
          }
        }
      } else {
        return create<T1>(l, std::move(x), d, r);
      }
    }
  }

  template <typename T1>
  static tree<T1> add(typename X::t x, T1 d, const tree<T1> &m) {
    if (std::holds_alternative<typename tree<T1>::Leaf>(m.v())) {
      return tree<T1>::node(tree<T1>::leaf(), x, std::move(d), tree<T1>::leaf(),
                            I::_1);
    } else {
      const auto &[a0, a1, a2, a3, a4] =
          std::get<typename tree<T1>::Node>(m.v());
      auto &&_sv = X::compare(x, a1);
      if (std::holds_alternative<typename Compare<typename X::t>::LT>(
              _sv.v())) {
        return bal<T1>(add<T1>(x, std::move(d), *a0), a1, a2, *a3);
      } else if (std::holds_alternative<typename Compare<typename X::t>::EQ>(
                     _sv.v())) {
        return tree<T1>::node(*a0, a1, std::move(d), *a3, a4);
      } else {
        return bal<T1>(*a0, a1, a2, add<T1>(x, std::move(d), *a3));
      }
    }
  }

  template <typename T1>
  static std::pair<tree<T1>, std::pair<key, T1>>
  remove_min(const tree<T1> &l, typename X::t x, T1 d, tree<T1> r) {
    if (std::holds_alternative<typename tree<T1>::Leaf>(l.v())) {
      return std::make_pair(std::move(r), std::make_pair(x, d));
    } else {
      const auto &[a0, a1, a2, a3, a4] =
          std::get<typename tree<T1>::Node>(l.v());
      auto [l_, m] = remove_min<T1>(*a0, a1, a2, *a3);
      return std::make_pair(bal<T1>(std::move(l_), x, d, std::move(r)),
                            std::move(m));
    }
  }

  template <typename T1> static tree<T1> merge(tree<T1> s1, tree<T1> s2) {
    if (std::holds_alternative<typename tree<T1>::Leaf>(s1.v_mut())) {
      return s2;
    } else {
      if (std::holds_alternative<typename tree<T1>::Leaf>(s2.v_mut())) {
        return s1;
      } else {
        auto &[a00, a10, a20, a30, a40] =
            std::get<typename tree<T1>::Node>(s2.v_mut());
        auto [s2_, p] =
            remove_min<T1>(*a00, std::move(a10), std::move(a20), *a30);
        auto [x, d] = std::move(p);
        return bal<T1>(s1, x, d, std::move(s2_));
      }
    }
  }

  template <typename T1>
  static tree<T1> remove(typename X::t x, const tree<T1> &m) {
    if (std::holds_alternative<typename tree<T1>::Leaf>(m.v())) {
      return tree<T1>::leaf();
    } else {
      const auto &[a0, a1, a2, a3, a4] =
          std::get<typename tree<T1>::Node>(m.v());
      auto &&_sv = X::compare(x, a1);
      if (std::holds_alternative<typename Compare<typename X::t>::LT>(
              _sv.v())) {
        return bal<T1>(remove<T1>(x, *a0), a1, a2, *a3);
      } else if (std::holds_alternative<typename Compare<typename X::t>::EQ>(
                     _sv.v())) {
        return merge<T1>(*a0, *a3);
      } else {
        return bal<T1>(*a0, a1, a2, remove<T1>(x, *a3));
      }
    }
  }

  template <typename T1>
  static tree<T1> join(const tree<T1> &l, key x0_, const T1 &x1_,
                       tree<T1> x2_) {
    return
        [=]() mutable -> std::function<tree<T1>(typename X::t, T1, tree<T1>)> {
          if (std::holds_alternative<typename tree<T1>::Leaf>(l.v())) {
            return add<T1>;
          } else {
            const auto &[a0, a1, a2, a3, a4] =
                std::get<typename tree<T1>::Node>(l.v());
            const tree<T1> &a0_value = *a0;
            const tree<T1> &a3_value = *a3;
            return [=](typename X::t x, T1 d) mutable {
              auto join_aux_impl = [=](auto &_self_join_aux,
                                       tree<T1> r) mutable -> tree<T1> {
                if (std::holds_alternative<typename tree<T1>::Leaf>(r.v())) {
                  return add<T1>(x, d, l);
                } else {
                  const auto &[a5, a6, a7, a8, a9] =
                      std::get<typename tree<T1>::Node>(r.v());
                  if (I::gt_le_dec(a4, I::add(a9, I::_2))) {
                    return bal<T1>(a0_value, a1, a2,
                                   join<T1>(a3_value, x, d, r));
                  } else {
                    if (I::gt_le_dec(a9, I::add(a4, I::_2))) {
                      return bal<T1>(_self_join_aux(_self_join_aux, *a5), a6,
                                     a7, *a8);
                    } else {
                      return create<T1>(l, x, d, r);
                    }
                  }
                }
              };
              auto join_aux = [=](tree<T1> r) mutable -> tree<T1> {
                return join_aux_impl(join_aux_impl, r);
              };
              return join_aux;
            };
          }
        }()(std::move(x0_), x1_, std::move(x2_));
  }

  template <typename elt> struct triple {
    tree<elt> t_left;
    std::optional<elt> t_opt;
    tree<elt> t_right;

    // ACCESSORS
    template <typename _U> operator triple<_U>() const {
      return {crane_convert<tree<_U>>(t_left), std::optional<_U>(t_opt),
              crane_convert<tree<_U>>(t_right)};
    }
  };

  template <typename T1>
  static triple<T1> split(typename X::t x, const tree<T1> &m) {
    if (std::holds_alternative<typename tree<T1>::Leaf>(m.v())) {
      return triple<T1>{tree<T1>::leaf(), std::optional<T1>(),
                        tree<T1>::leaf()};
    } else {
      const auto &[a0, a1, a2, a3, a4] =
          std::get<typename tree<T1>::Node>(m.v());
      auto &&_sv = X::compare(x, a1);
      if (std::holds_alternative<typename Compare<typename X::t>::LT>(
              _sv.v())) {
        tree<T1> ll = split<T1>(x, *a0).t_left;
        std::optional<T1> o = split<T1>(x, *a0).t_opt;
        tree<T1> rl = split<T1>(x, *a0).t_right;
        return triple<T1>{std::move(ll), std::move(o),
                          join<T1>(std::move(rl), a1, a2, *a3)};
      } else if (std::holds_alternative<typename Compare<typename X::t>::EQ>(
                     _sv.v())) {
        return triple<T1>{*a0, std::make_optional<T1>(a2), *a3};
      } else {
        tree<T1> rl = split<T1>(x, *a3).t_left;
        std::optional<T1> o = split<T1>(x, *a3).t_opt;
        tree<T1> rr = split<T1>(x, *a3).t_right;
        return triple<T1>{join<T1>(*a0, a1, a2, std::move(rl)), std::move(o),
                          std::move(rr)};
      }
    }
  }

  template <typename T1> static tree<T1> concat(tree<T1> m1, tree<T1> m2) {
    if (std::holds_alternative<typename tree<T1>::Leaf>(m1.v_mut())) {
      return m2;
    } else {
      if (std::holds_alternative<typename tree<T1>::Leaf>(m2.v_mut())) {
        return m1;
      } else {
        auto &[a00, a10, a20, a30, a40] =
            std::get<typename tree<T1>::Node>(m2.v_mut());
        auto [m2_, xd] =
            remove_min<T1>(*a00, std::move(a10), std::move(a20), *a30);
        return join<T1>(m1, xd.first, xd.second, std::move(m2_));
      }
    }
  }

  template <typename T1>
  static List<std::pair<key, T1>>
  elements_aux(List<std::pair<typename X::t, T1>> acc, const tree<T1> &m) {
    if (std::holds_alternative<typename tree<T1>::Leaf>(m.v())) {
      return acc;
    } else {
      const auto &[a0, a1, a2, a3, a4] =
          std::get<typename tree<T1>::Node>(m.v());
      return elements_aux<T1>(
          List<std::pair<typename X::t, T1>>::cons(
              std::make_pair(a1, a2), elements_aux<T1>(std::move(acc), *a3)),
          *a0);
    }
  }

  template <typename T1>
  static List<std::pair<key, T1>> elements(const tree<T1> &m) {
    return elements_aux<T1>(List<std::pair<typename X::t, T1>>::nil(), m);
  }

  template <typename T1, typename T2, typename F0>
    requires std::is_invocable_r_v<T2, F0 &, typename X::t &, T1 &, T2 &>
  static T2 fold(F0 &&f, const tree<T1> &m, T2 a) {
    if (std::holds_alternative<typename tree<T1>::Leaf>(m.v())) {
      return a;
    } else {
      const auto &[a0, a1, a2, a3, a4] =
          std::get<typename tree<T1>::Node>(m.v());
      return fold<T1, T2>(f, *a3,
                          f(a1, a2, fold<T1, T2>(f, *a0, std::move(a))));
    }
  }

  template <typename elt> struct enumeration {
    // TYPES
    struct End {};

    struct More {
      key a0;
      elt a1;
      tree<elt> a2;
      std::shared_ptr<enumeration<elt>> a3;
    };

    using variant_t = std::variant<End, More>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    enumeration() {}

    explicit enumeration(End _v) : v_(_v) {}

    explicit enumeration(More _v) : v_(std::move(_v)) {}

    template <typename _U> enumeration(const enumeration<_U> &_other) {
      if (std::holds_alternative<typename enumeration<_U>::End>(_other.v())) {
        this->v_ = End{};
      } else {
        const auto &[a0, a1, a2, a3] =
            std::get<typename enumeration<_U>::More>(_other.v());
        this->v_ =
            More{a0,
                 [&]() -> elt {
                   if constexpr (crane_convertible<elt, const _U &>) {
                     return crane_convert<elt>(a1);
                   } else {
                     throw std::logic_error("unreachable: inactive constructor "
                                            "field at this instantiation");
                   }
                 }(),
                 crane_convert<tree<elt>>(a2),
                 (a3 ? std::make_shared<enumeration<elt>>(
                           crane_convert<enumeration<elt>>(*a3))
                     : nullptr)};
      }
    }

    static enumeration<elt> end() { return enumeration<elt>(End{}); }

    static enumeration<elt> more(key a0, elt a1, tree<elt> a2,
                                 enumeration<elt> a3) {
      return enumeration<elt>(
          More{std::move(a0), std::move(a1), std::move(a2),
               std::make_shared<enumeration<elt>>(std::move(a3))});
    }

    // MANIPULATORS
    ~enumeration() {
      crane::small_vector<std::shared_ptr<enumeration<elt>>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<More>(&_v)) {
          if (_alt->a3) {
            _stack.push_back(std::move(_alt->a3));
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

    enumeration(const enumeration &) = default;
    enumeration &operator=(const enumeration &) = default;
    enumeration(enumeration &&) noexcept = default;
    enumeration &operator=(enumeration &&) noexcept = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename T2, typename F1>
    requires std::is_invocable_r_v<T2, F1 &, typename X::t &, T1 &, tree<T1> &,
                                   enumeration<T1> &, T2 &>
  static T2 enumeration_rect(T2 f, F1 &&f0, const enumeration<T1> &e) {
    if (std::holds_alternative<typename enumeration<T1>::End>(e.v())) {
      return f;
    } else {
      const auto &[a0, a1, a2, a3] =
          std::get<typename enumeration<T1>::More>(e.v());
      return f0(a0, a1, a2, *a3,
                enumeration_rect<T1, T2>(std::move(f), f0, *a3));
    }
  }

  template <typename T1, typename T2, typename F1>
    requires std::is_invocable_r_v<T2, F1 &, typename X::t &, T1 &, tree<T1> &,
                                   enumeration<T1> &, T2 &>
  static T2 enumeration_rec(T2 f, F1 &&f0, const enumeration<T1> &e) {
    if (std::holds_alternative<typename enumeration<T1>::End>(e.v())) {
      return f;
    } else {
      const auto &[a0, a1, a2, a3] =
          std::get<typename enumeration<T1>::More>(e.v());
      return f0(a0, a1, a2, *a3,
                enumeration_rec<T1, T2>(std::move(f), f0, *a3));
    }
  }

  template <typename T1>
  static enumeration<T1> cons(const tree<T1> &m, enumeration<T1> e) {
    if (std::holds_alternative<typename tree<T1>::Leaf>(m.v())) {
      return e;
    } else {
      const auto &[a0, a1, a2, a3, a4] =
          std::get<typename tree<T1>::Node>(m.v());
      return cons<T1>(*a0, enumeration<T1>::more(a1, a2, *a3, std::move(e)));
    }
  }

  template <typename T1, typename F0, typename F3>
    requires std::is_invocable_r_v<bool, F0 &, T1 &, T1 &> &&
             std::is_invocable_r_v<bool, F3 &, enumeration<T1> &>
  static bool equal_more(F0 &&cmp, typename X::t x1, const T1 &d1, F3 &&cont,
                         const enumeration<T1> &e2) {
    if (std::holds_alternative<typename enumeration<T1>::End>(e2.v())) {
      return false;
    } else {
      const auto &[a0, a1, a2, a3] =
          std::get<typename enumeration<T1>::More>(e2.v());
      auto &&_sv = X::compare(x1, a0);
      if (std::holds_alternative<typename Compare<typename X::t>::EQ>(
              _sv.v())) {
        if (cmp(d1, a1)) {
          return cont(cons<T1>(a2, *a3));
        } else {
          return false;
        }
      } else {
        return false;
      }
    }
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<bool, F0 &, T1 &, T1 &>
  static bool equal_cont(F0 &&cmp, const tree<T1> &m1,
                         std::function<bool(enumeration<T1>)> cont,
                         const enumeration<T1> &e2) {
    if (std::holds_alternative<typename tree<T1>::Leaf>(m1.v())) {
      return cont(e2);
    } else {
      const auto &[a0, a1, a2, a3, a4] =
          std::get<typename tree<T1>::Node>(m1.v());
      const tree<T1> &a0_value = *a0;
      const tree<T1> &a3_value = *a3;
      return equal_cont<T1>(
          cmp, a0_value,
          [=](enumeration<T1> _x0) mutable -> bool {
            return equal_more<T1>(
                cmp, a1, a2,
                [=](enumeration<T1> _x0) mutable -> bool {
                  return equal_cont<T1>(cmp, a3_value, cont, _x0);
                },
                _x0);
          },
          e2);
    }
  }

  template <typename T1> static bool equal_end(const enumeration<T1> &e2) {
    if (std::holds_alternative<typename enumeration<T1>::End>(e2.v())) {
      return true;
    } else {
      return false;
    }
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<bool, F0 &, T1 &, T1 &>
  static bool equal(F0 &&cmp, const tree<T1> &m1, const tree<T1> &m2) {
    return equal_cont<T1>(cmp, m1, equal_end<T1>,
                          cons<T1>(m2, enumeration<T1>::end()));
  }

  template <typename T1, typename T2, typename F0>
    requires std::is_invocable_r_v<T2, F0 &, T1 &>
  static tree<T2> map(F0 &&f, const tree<T1> &m) {
    if (std::holds_alternative<typename tree<T1>::Leaf>(m.v())) {
      return tree<T2>::leaf();
    } else {
      const auto &[a0, a1, a2, a3, a4] =
          std::get<typename tree<T1>::Node>(m.v());
      return tree<T2>::node(map<T1, T2>(f, *a0), a1, f(a2), map<T1, T2>(f, *a3),
                            a4);
    }
  }

  template <typename T1, typename T2, typename F0>
    requires std::is_invocable_r_v<T2, F0 &, typename X::t &, T1 &>
  static tree<T2> mapi(F0 &&f, const tree<T1> &m) {
    if (std::holds_alternative<typename tree<T1>::Leaf>(m.v())) {
      return tree<T2>::leaf();
    } else {
      const auto &[a0, a1, a2, a3, a4] =
          std::get<typename tree<T1>::Node>(m.v());
      return tree<T2>::node(mapi<T1, T2>(f, *a0), a1, f(a1, a2),
                            mapi<T1, T2>(f, *a3), a4);
    }
  }

  template <typename T1, typename T2, typename F0>
    requires std::is_invocable_r_v<std::optional<T2>, F0 &, typename X::t &,
                                   T1 &>
  static tree<T2> map_option(F0 &&f, const tree<T1> &m) {
    if (std::holds_alternative<typename tree<T1>::Leaf>(m.v())) {
      return tree<T2>::leaf();
    } else {
      const auto &[a0, a1, a2, a3, a4] =
          std::get<typename tree<T1>::Node>(m.v());
      auto _cs = f(a1, a2);
      if (_cs.has_value()) {
        const T2 &d_ = *_cs;
        return join<T2>(map_option<T1, T2>(f, *a0), a1, d_,
                        map_option<T1, T2>(f, *a3));
      } else {
        return concat<T2>(map_option<T1, T2>(f, *a0),
                          map_option<T1, T2>(f, *a3));
      }
    }
  }

  template <typename T1, typename T2, typename T3, typename F0, typename F1,
            typename F2>
    requires std::is_invocable_r_v<std::optional<T3>, F0 &, typename X::t &,
                                   T1 &, std::optional<T2> &> &&
             std::is_invocable_r_v<tree<T3>, F1 &, tree<T1> &> &&
             std::is_invocable_r_v<tree<T3>, F2 &, tree<T2> &>
  static tree<T3> map2_opt(F0 &&f, F1 &&mapl, F2 &&mapr, const tree<T1> &m1,
                           const tree<T2> &m2) {
    if (std::holds_alternative<typename tree<T1>::Leaf>(m1.v())) {
      return mapr(m2);
    } else {
      const auto &[a0, a1, a2, a3, a4] =
          std::get<typename tree<T1>::Node>(m1.v());
      if (std::holds_alternative<typename tree<T2>::Leaf>(m2.v())) {
        return mapl(m1);
      } else {
        tree<T2> l2_ = split<T2>(a1, m2).t_left;
        std::optional<T2> o2 = split<T2>(a1, m2).t_opt;
        tree<T2> r2_ = split<T2>(a1, m2).t_right;
        auto _cs = f(a1, a2, std::move(o2));
        if (_cs.has_value()) {
          const T3 &e = *_cs;
          return join<T3>(
              map2_opt<T1, T2, T3>(f, mapl, mapr, *a0, std::move(l2_)), a1, e,
              map2_opt<T1, T2, T3>(f, mapl, mapr, *a3, std::move(r2_)));
        } else {
          return concat<T3>(
              map2_opt<T1, T2, T3>(f, mapl, mapr, *a0, std::move(l2_)),
              map2_opt<T1, T2, T3>(f, mapl, mapr, *a3, std::move(r2_)));
        }
      }
    }
  }

  template <typename T1, typename T2, typename T3, typename F0>
    requires std::is_invocable_r_v<std::optional<T3>, F0 &, std::optional<T1> &,
                                   std::optional<T2> &>
  static tree<T3> map2(F0 &&f, const tree<T1> &x0_, tree<T2> x1_) {
    return map2_opt<T1, T2, T3>(
        [=](typename X::t, T1 d, const std::optional<T2> &o) mutable {
          return f(std::make_optional<T1>(d), o);
        },
        [=](tree<T1> _x0) mutable -> tree<T3> {
          return map_option<T1, T3>(
              [=](typename X::t, T1 d) mutable {
                return f(std::make_optional<T1>(d), std::optional<T2>());
              },
              _x0);
        },
        [=](tree<T2> _x0) mutable -> tree<T3> {
          return map_option<T2, T3>(
              [=](typename X::t, T2 d_) mutable {
                return f(std::optional<T1>(), std::make_optional<T2>(d_));
              },
              _x0);
        },
        x0_, std::move(x1_));
  }

  struct Proofs {
    using MX = OrderedTypeFacts<X>;
    using PX = KeyOrderedType<X>;
    using L = Coq_Raw<X>;

    template <typename T1, typename T2, typename F0>
      requires std::is_invocable_r_v<T2, F0 &, typename X::t &, T1 &, T2 &>
    static T2 fold_(F0 &&f, tree<T1> s, T2 x0_) {
      return L::template fold<T1, T2>(f, elements<T1>(std::move(s)),
                                      std::move(x0_));
    }

    template <typename T1>
    static List<std::pair<key, T1>> flatten_e(const enumeration<T1> &e) {
      if (std::holds_alternative<typename enumeration<T1>::End>(e.v())) {
        return List<std::pair<key, T1>>::nil();
      } else {
        const auto &[a0, a1, a2, a3] =
            std::get<typename enumeration<T1>::More>(e.v());
        return List<std::pair<key, T1>>::cons(
            std::make_pair(a0, a1), elements<T1>(a2).app(flatten_e<T1>(*a3)));
      }
    }
  };
};

template <Int I, OrderedType X> struct IntMake {
  using E = X;
  using Raw = Raw<I, X>;

  template <typename elt> struct bst {
    typename Raw::template tree<elt> this_;

    // ACCESSORS
    template <typename _U> operator bst<_U>() const {
      return {crane_convert<typename Raw::template tree<_U>>(this_)};
    }
  };

  template <typename elt> using t = bst<elt>;
  using key = typename E::t;

  template <typename T1> static const t<T1> &empty() {
    static const t<T1> v = bst<T1>{Raw::template empty<T1>()};
    return v;
  }

  template <typename T1> static bool is_empty(const bst<T1> &m) {
    return Raw::template is_empty<T1>(m.this_);
  }

  template <typename T1>
  static t<T1> add(typename X::t x, const T1 &e, const bst<T1> &m) {
    return bst<T1>{Raw::template add<T1>(std::move(x), e, m.this_)};
  }

  template <typename T1>
  static t<T1> remove(typename X::t x, const bst<T1> &m) {
    return bst<T1>{Raw::template remove<T1>(std::move(x), m.this_)};
  }

  template <typename T1> static bool mem(typename X::t x, const bst<T1> &m) {
    return Raw::template mem<T1>(std::move(x), m.this_);
  }

  template <typename T1>
  static std::optional<T1> find(typename X::t x, const bst<T1> &m) {
    return Raw::template find<T1>(std::move(x), m.this_);
  }

  template <typename T1, typename T2, typename F0>
    requires std::is_invocable_r_v<T2, F0 &, T1 &>
  static t<T2> map(F0 &&f, const bst<T1> &m) {
    return bst<T2>{Raw::template map<T1, T2>(f, m.this_)};
  }

  template <typename T1, typename T2, typename F0>
    requires std::is_invocable_r_v<T2, F0 &, typename X::t &, T1 &>
  static t<T2> mapi(F0 &&f, const bst<T1> &m) {
    return bst<T2>{Raw::template mapi<T1, T2>(f, m.this_)};
  }

  template <typename T1, typename T2, typename T3, typename F0>
    requires std::is_invocable_r_v<std::optional<T3>, F0 &, std::optional<T1> &,
                                   std::optional<T2> &>
  static t<T3> map2(F0 &&f, const bst<T1> &m, const bst<T2> &m_) {
    return bst<T3>{Raw::template map2<T1, T2, T3>(f, m.this_, m_.this_)};
  }

  template <typename T1>
  static List<std::pair<key, T1>> elements(const bst<T1> &m) {
    return Raw::template elements<T1>(m.this_);
  }

  template <typename T1> static Nat cardinal(const bst<T1> &m) {
    return Raw::template cardinal<T1>(m.this_);
  }

  template <typename T1, typename T2, typename F0>
    requires std::is_invocable_r_v<T2, F0 &, typename X::t &, T1 &, T2 &>
  static T2 fold(F0 &&f, const bst<T1> &m, const T2 &i) {
    return Raw::template fold<T1, T2>(f, m.this_, i);
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<bool, F0 &, T1 &, T1 &>
  static bool equal(F0 &&cmp, const bst<T1> &m, const bst<T1> &m_) {
    return Raw::template equal<T1>(cmp, m.this_, m_.this_);
  }
};

template <OrderedType X> struct Make : IntMake<Z_as_Int, X> {};

using IM = Make<Z_as_OT>;

template <typename T1> Nat raw_size(const IM::Raw::tree<T1> &x0_) {
  return IM::Raw::template cardinal<T1>(x0_);
}

template <typename T1> Nat im_size(const IM::template bst<T1> &m) {
  return raw_size<T1>(m.this_);
}

struct Qp {
  static Nat use(IM::template t<Nat> x0_);
};

#endif // INCLUDED_FUNCTOR_RECORD_PROJ_AS_STATIC
