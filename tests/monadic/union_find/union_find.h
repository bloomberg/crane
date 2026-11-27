#pragma once

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include "small_vector.h"
#include <atomic>
#include <concepts>
#include <crane_itree.h>
#include <crane_st.h>
#include <cstdint>
#include <memory>
#include <optional>
#include <span>
#include <stdexcept>
#include <string>
#include <string_view>
#include <type_traits>
#include <utility>
#include <variant>

template <typename T1> struct code_const;
template <typename A> struct List;
enum class Comparison;
struct Positive;
struct Z;
template <typename Err> struct ExceptE;
struct Err;
template <typename X> struct Compare;
enum class STRefs;
struct Op;
template <typename I, typename V, typename A>
concept Code = requires {
  { I::code() } -> std::convertible_to<uint64_t>;
};

struct Datatypes {
  static Comparison CompOpp(Comparison r);
};

struct Nat {};

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

  static List<A> cons(A a, crane::shared_child_slot<List<A>> l) {
    return List<A>(Cons{std::move(a), l.take()});
  }

  // MANIPULATORS
  ~List() {
    // Release the children this node alone owns in a loop, not recursively, so
    // a deep value cannot overflow the stack.
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
    requires std::is_invocable_r_v<T1, F0 &, A &, T1 &&>
  T1 fold_right(F0 &&f, T1 a0) const {
    const List<A> *_self = this;

    // Explicit stack replaces the non-tail recursion of fold_right: _call
    // frames are pending calls, _after frames resume a caller.
    struct _call {
      const List<A> *_self;
    };

    struct _after_fold_right_in_Cons {
      A a1;
    };

    using _frame = std::variant<_call, _after_fold_right_in_Cons>;
    T1 _result{};
    crane::small_vector<_frame> _stack;
    _stack.emplace_back(_call{_self});
    while (!_stack.empty()) {
      _frame &_popped = _stack.back();
      if (std::holds_alternative<_call>(_popped)) {
        auto _f = std::move(std::get<_call>(_popped));
        _stack.pop_back();
        const List<A> *_self = _f._self;
        auto &&_sv = *_self;
        if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
          _result = a0;
        } else {
          const auto &[a1, a2] = std::get<typename List<A>::Cons>(_sv.v());
          _stack.emplace_back(_after_fold_right_in_Cons{a1});
          _stack.emplace_back(_call{crane_raw(a2)});
        }
      } else {
        auto _f = std::move(std::get<_after_fold_right_in_Cons>(_popped));
        _stack.pop_back();
        auto a1 = std::move(_f.a1);
        _result = f(a1, std::move(_result));
      }
    }
    return _result;
  }

  List<A> app(List<A> m) const {
    // Builds the result front to back: _write points at the empty tail the next
    // cell fills.
    std::optional<List<A>> _root{};
    std::shared_ptr<List<A>> *_write = nullptr;
    const List<A> *_loop_self = this;
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
        auto _value = std::move(m);
        (_write ? *(*_write = std::make_shared<List<A>>(std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[a0, a1] = std::get<typename List<A>::Cons>(_sv.v());
        auto _cell = typename List<A>::Cons(a0, nullptr);
        List<A> &_node =
            (_write ? *(*_write = std::make_shared<List<A>>(std::move(_cell)))
                    : _root.emplace(std::move(_cell)));
        _write = &std::get<typename List<A>::Cons>(_node.v_mut()).l;
        _loop_self = crane_raw(a1);
        continue;
      }
    }
    return std::move(*_root);
  }
};

enum class Comparison { EQ, LT, GT };
template <typename M>
concept EqLtLe = requires {
  typename M::t;
};

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

  static Positive xi(crane::shared_child_slot<Positive> a0) {
    return Positive(XI{a0.take()});
  }

  static Positive xo(crane::shared_child_slot<Positive> a0) {
    return Positive(XO{a0.take()});
  }

  static Positive xh() { return Positive(XH{}); }

  // MANIPULATORS
  ~Positive() {
    // Release the children this node alone owns in a loop, not recursively, so
    // a deep value cannot overflow the stack.
    auto _next = [&](variant_t &_v) -> std::shared_ptr<Positive> {
      if (auto *_alt = std::get_if<XI>(&_v)) {
        if (_alt->a0 && _alt->a0.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          return std::move(_alt->a0);
        }
      }
      if (auto *_alt = std::get_if<XO>(&_v)) {
        if (_alt->a0 && _alt->a0.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          return std::move(_alt->a0);
        }
      }
      return nullptr;
    };
    std::shared_ptr<Positive> _cur = _next(v_mut());
    while (_cur) {
      _cur = _next(_cur->v_mut());
    }
  }

  Positive(const Positive &) = default;
  Positive &operator=(const Positive &) = default;
  Positive(Positive &&) = default;
  Positive &operator=(Positive &&) = default;

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

template <typename Err> struct ExceptE {
  // DATA
  Err a0;

  // ACCESSORS
  ExceptE<Err> clone() const { return {a0}; }

  template <typename CraneU> operator ExceptE<CraneU>() const {
    return {[&]() -> CraneU {
      if constexpr (crane_convertible<CraneU, const Err &>) {
        return crane_convert<CraneU>(a0);
      } else {
        throw std::logic_error("unreachable: inactive constructor field at "
                               "this instantiation");
      }
    }()};
  }

  // CREATORS
  static ExceptE<Err> Throw_(Err a0) { return {std::move(a0)}; }
};

template <EqLtLe O, typename P> struct MakeOrderTac {};

struct Err {
  // DATA
  std::string x;

  // ACCESSORS
  Err clone() const { return {x}; }

  // CREATORS
  static Err error(std::string x) { return {std::move(x)}; }
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
    auto &&_sv = O::compare(std::move(x), std::move(y));
    if (std::holds_alternative<typename Compare<typename O::t>::LT>(_sv.v())) {
      return true;
    } else {
      return false;
    }
  }

  static bool eqb(typename O::t x, typename O::t y) {
    if (eq_dec(std::move(x), std::move(y))) {
      return true;
    } else {
      return false;
    }
  }
};

template <OrderedType O> struct KeyOrderedType {
  using MO = OrderedTypeFacts<O>;
};

struct BinInt {
  static Z double_(const Z &x);
  static Z succ_double(const Z &x);
  static Z pred_double(const Z &x);
  static Z pos_sub(const Positive &x, const Positive &y);
  static Z add(const Z &x, const Z &y);
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

enum class STRefs { BUILD_STREFS };

template <typename T1> struct code_const {
  constexpr static uint64_t code() { return UINT64_C(0); }
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
    if (std::holds_alternative<typename List<std::pair<typename X::t,
                                                       T1>>::Nil>(l.v())) {
      return true;
    } else {
      return false;
    }
  }

  template <typename T1>
  static bool mem(typename X::t k,
                  const List<std::pair<typename X::t, T1>> &s) {
    // Loop replaces the tail recursion: each recursive call updates the loop
    // variables.
    const List<std::pair<typename X::t, T1>> *_loop_s = &s;
    while (true) {
      if (std::holds_alternative<
              typename List<std::pair<typename X::t, T1>>::Nil>(_loop_s->v())) {
        return false;
      } else {
        const auto &[a0, a1] =
            std::get<typename List<std::pair<typename X::t, T1>>::Cons>(
                _loop_s->v());
        const auto &[k_, _] = a0;
        auto &&_sv = X::compare(k, k_);
        if (std::holds_alternative<typename Compare<typename X::t>::LT>(_sv.v())) {
          return false;
        } else if (std::holds_alternative<typename Compare<typename X::t>::EQ>(
                       _sv.v())) {
          return true;
        } else {
          _loop_s = crane_raw(a1);
        }
      }
    }
  }

  template <typename T1>
  static std::optional<T1> find(typename X::t k,
                                const List<std::pair<typename X::t, T1>> &s) {
    // Loop replaces the tail recursion: each recursive call updates the loop
    // variables.
    const List<std::pair<typename X::t, T1>> *_loop_s = &s;
    while (true) {
      if (std::holds_alternative<
              typename List<std::pair<typename X::t, T1>>::Nil>(_loop_s->v())) {
        return std::optional<T1>();
      } else {
        const auto &[a0, a1] =
            std::get<typename List<std::pair<typename X::t, T1>>::Cons>(
                _loop_s->v());
        const auto &[k_, x] = a0;
        auto &&_sv = X::compare(k, k_);
        if (std::holds_alternative<typename Compare<typename X::t>::LT>(_sv.v())) {
          return std::optional<T1>();
        } else if (std::holds_alternative<typename Compare<typename X::t>::EQ>(
                       _sv.v())) {
          return std::make_optional<T1>(x);
        } else {
          _loop_s = crane_raw(a1);
        }
      }
    }
  }

  template <typename T1>
  static t<T1> add(typename X::t k, const T1 &x,
                   const List<std::pair<typename X::t, T1>> &s) {
    // Builds the result front to back: _write points at the empty tail the next
    // cell fills.
    std::optional<t<T1>> _root{};
    std::shared_ptr<t<T1>> *_write = nullptr;
    const List<std::pair<typename X::t, T1>> *_loop_s = &s;
    while (true) {
      if (std::holds_alternative<
              typename List<std::pair<typename X::t, T1>>::Nil>(_loop_s->v())) {
        auto _value = List<std::pair<typename X::t, T1>>::cons(
            std::make_pair(std::move(k), x),
            List<std::pair<typename X::t, T1>>::nil());
        (_write ? *(*_write = std::make_shared<t<T1>>(std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[a0, a1] =
            std::get<typename List<std::pair<typename X::t, T1>>::Cons>(
                _loop_s->v());
        const auto &[k_, y] = a0;
        auto &&_sv = X::compare(k, k_);
        if (std::holds_alternative<typename Compare<typename X::t>::LT>(_sv.v())) {
          auto _value = List<std::pair<typename X::t, T1>>::cons(
              std::make_pair(std::move(k), x), crane::shared_child(_loop_s));
          (_write ? *(*_write = std::make_shared<t<T1>>(std::move(_value)))
                  : _root.emplace(std::move(_value)));
          break;
        } else if (std::holds_alternative<typename Compare<typename X::t>::EQ>(
                       _sv.v())) {
          auto _value = List<std::pair<typename X::t, T1>>::cons(
              std::make_pair(std::move(k), x), crane::shared_child(a1));
          (_write ? *(*_write = std::make_shared<t<T1>>(std::move(_value)))
                  : _root.emplace(std::move(_value)));
          break;
        } else {
          auto _cell = typename List<std::pair<typename X::t, T1>>::Cons(
              std::make_pair(k_, y), nullptr);
          t<T1> &_node =
              (_write ? *(*_write = std::make_shared<t<T1>>(std::move(_cell)))
                      : _root.emplace(std::move(_cell)));
          _write =
              &std::get<typename List<std::pair<typename X::t, T1>>::Cons>(
                  _node.v_mut())
                  .l;
          _loop_s = crane_raw(a1);
          continue;
        }
      }
    }
    return std::move(*_root);
  }

  template <typename T1>
  static t<T1> remove(typename X::t k,
                      const List<std::pair<typename X::t, T1>> &s) {
    // Builds the result front to back: _write points at the empty tail the next
    // cell fills.
    std::optional<t<T1>> _root{};
    std::shared_ptr<t<T1>> *_write = nullptr;
    const List<std::pair<typename X::t, T1>> *_loop_s = &s;
    while (true) {
      if (std::holds_alternative<
              typename List<std::pair<typename X::t, T1>>::Nil>(_loop_s->v())) {
        auto _value = List<std::pair<typename X::t, T1>>::nil();
        (_write ? *(*_write = std::make_shared<t<T1>>(std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[a0, a1] =
            std::get<typename List<std::pair<typename X::t, T1>>::Cons>(
                _loop_s->v());
        const auto &[k_, x] = a0;
        auto &&_sv = X::compare(k, k_);
        if (std::holds_alternative<typename Compare<typename X::t>::LT>(_sv.v())) {
          auto _value = *_loop_s;
          (_write ? *(*_write = std::make_shared<t<T1>>(std::move(_value)))
                  : _root.emplace(std::move(_value)));
          break;
        } else if (std::holds_alternative<typename Compare<typename X::t>::EQ>(
                       _sv.v())) {
          auto _value = *a1;
          (_write ? *(*_write = std::make_shared<t<T1>>(std::move(_value)))
                  : _root.emplace(std::move(_value)));
          break;
        } else {
          auto _cell = typename List<std::pair<typename X::t, T1>>::Cons(
              std::make_pair(k_, x), nullptr);
          t<T1> &_node =
              (_write ? *(*_write = std::make_shared<t<T1>>(std::move(_cell)))
                      : _root.emplace(std::move(_cell)));
          _write =
              &std::get<typename List<std::pair<typename X::t, T1>>::Cons>(
                  _node.v_mut())
                  .l;
          _loop_s = crane_raw(a1);
          continue;
        }
      }
    }
    return std::move(*_root);
  }

  template <typename T1>
  static t<T1> elements(List<std::pair<typename X::t, T1>> m) {
    return m;
  }

  template <typename T1, typename T2, typename F0>
  static T2 fold(F0 &&f, const List<std::pair<typename X::t, T1>> &m, T2 acc) {
    // Loop replaces the tail recursion: each recursive call updates the loop
    // variables.
    T2 _loop_acc = std::move(acc);
    const List<std::pair<typename X::t, T1>> *_loop_m = &m;
    while (true) {
      if (std::holds_alternative<
              typename List<std::pair<typename X::t, T1>>::Nil>(_loop_m->v())) {
        return _loop_acc;
      } else {
        const auto &[a0, a1] =
            std::get<typename List<std::pair<typename X::t, T1>>::Cons>(
                _loop_m->v());
        const auto &[k, e] = a0;
        _loop_acc = f(k, e, std::move(_loop_acc));
        _loop_m = crane_raw(a1);
      }
    }
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<bool, F0 &, T1 &, T1 &>
  static bool equal(F0 &&cmp, const List<std::pair<typename X::t, T1>> &m,
                    const List<std::pair<typename X::t, T1>> &m_) {
    // Explicit stack replaces the non-tail recursion of equal: _call frames are
    // pending calls, _after frames resume a caller.
    struct _call {
      const List<std::pair<typename X::t, T1>> *m_;
      const List<std::pair<typename X::t, T1>> *m;
    };

    struct _after_equal_in_EQ {
      T1 e;
      T1 e_;
    };

    using _frame = std::variant<_call, _after_equal_in_EQ>;
    bool _result{};
    crane::small_vector<_frame> _stack;
    _stack.emplace_back(_call{&m_, &m});
    while (!_stack.empty()) {
      _frame &_popped = _stack.back();
      if (std::holds_alternative<_call>(_popped)) {
        auto _f = std::move(std::get<_call>(_popped));
        _stack.pop_back();
        const List<std::pair<typename X::t, T1>> &m_ = *_f.m_;
        const List<std::pair<typename X::t, T1>> &m = *_f.m;
        if (std::holds_alternative<
                typename List<std::pair<typename X::t, T1>>::Nil>(m.v())) {
          if (std::holds_alternative<
                  typename List<std::pair<typename X::t, T1>>::Nil>(m_.v())) {
            _result = true;
          } else {
            _result = false;
          }
        } else {
          const auto &[a0, a1] = std::get<
              typename List<std::pair<typename X::t, T1>>::Cons>(m.v());
          const auto &[x, e] = a0;
          if (std::holds_alternative<
                  typename List<std::pair<typename X::t, T1>>::Nil>(m_.v())) {
            _result = false;
          } else {
            const auto &[a00, a10] =
                std::get<typename List<std::pair<typename X::t, T1>>::Cons>(
                    m_.v());
            const auto &[x_, e_] = a00;
            auto &&_sv = X::compare(x, x_);
            if (std::holds_alternative<typename Compare<typename X::t>::EQ>(
                    _sv.v())) {
              _stack.emplace_back(_after_equal_in_EQ{e, e_});
              _stack.emplace_back(_call{crane_raw(a10), crane_raw(a1)});
            } else {
              _result = false;
            }
          }
        }
      } else {
        auto _f = std::move(std::get<_after_equal_in_EQ>(_popped));
        _stack.pop_back();
        auto e = std::move(_f.e);
        auto e_ = std::move(_f.e_);
        _result = (cmp(e, e_) && _result);
      }
    }
    return _result;
  }

  template <typename T1, typename T2, typename F0>
  static t<T2> map(F0 &&f, const List<std::pair<typename X::t, T1>> &m) {
    // Builds the result front to back: _write points at the empty tail the next
    // cell fills.
    std::optional<t<T2>> _root{};
    std::shared_ptr<t<T2>> *_write = nullptr;
    const List<std::pair<typename X::t, T1>> *_loop_m = &m;
    while (true) {
      if (std::holds_alternative<
              typename List<std::pair<typename X::t, T1>>::Nil>(_loop_m->v())) {
        auto _value = List<std::pair<typename X::t, T2>>::nil();
        (_write ? *(*_write = std::make_shared<t<T2>>(std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[a0, a1] =
            std::get<typename List<std::pair<typename X::t, T1>>::Cons>(
                _loop_m->v());
        const auto &[k, e] = a0;
        auto _cell = typename List<std::pair<typename X::t, T2>>::Cons(
            std::make_pair(k, f(e)), nullptr);
        t<T2> &_node =
            (_write ? *(*_write = std::make_shared<t<T2>>(std::move(_cell)))
                    : _root.emplace(std::move(_cell)));
        _write =
            &std::get<typename List<std::pair<typename X::t, T2>>::Cons>(
                _node.v_mut())
                .l;
        _loop_m = crane_raw(a1);
        continue;
      }
    }
    return std::move(*_root);
  }

  template <typename T1, typename T2, typename F0>
  static t<T2> mapi(F0 &&f, const List<std::pair<typename X::t, T1>> &m) {
    // Builds the result front to back: _write points at the empty tail the next
    // cell fills.
    std::optional<t<T2>> _root{};
    std::shared_ptr<t<T2>> *_write = nullptr;
    const List<std::pair<typename X::t, T1>> *_loop_m = &m;
    while (true) {
      if (std::holds_alternative<
              typename List<std::pair<typename X::t, T1>>::Nil>(_loop_m->v())) {
        auto _value = List<std::pair<typename X::t, T2>>::nil();
        (_write ? *(*_write = std::make_shared<t<T2>>(std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[a0, a1] =
            std::get<typename List<std::pair<typename X::t, T1>>::Cons>(
                _loop_m->v());
        const auto &[k, e] = a0;
        auto _cell = typename List<std::pair<typename X::t, T2>>::Cons(
            std::make_pair(k, f(k, e)), nullptr);
        t<T2> &_node =
            (_write ? *(*_write = std::make_shared<t<T2>>(std::move(_cell)))
                    : _root.emplace(std::move(_cell)));
        _write =
            &std::get<typename List<std::pair<typename X::t, T2>>::Cons>(
                _node.v_mut())
                .l;
        _loop_m = crane_raw(a1);
        continue;
      }
    }
    return std::move(*_root);
  }

  template <typename T1>
  static List<std::pair<key, T1>>
  option_cons(typename X::t k, const std::optional<T1> &o,
              List<std::pair<typename X::t, T1>> l) {
    if (o.has_value()) {
      const T1 &e = *o;
      return List<std::pair<typename X::t, T1>>::cons(
          std::make_pair(std::move(k), e), std::move(l));
    } else {
      return l;
    }
  }

  template <typename T1, typename T2, typename T3, typename F0>
  static t<T3> map2_l(F0 &&f, const List<std::pair<typename X::t, T1>> &m) {
    // Explicit stack replaces the non-tail recursion of map2_l: _call frames
    // are pending calls, _after frames resume a caller.
    struct _call {
      const List<std::pair<typename X::t, T1>> *m;
    };

    struct _after_map2_l_in_pair {
      typename X::t k;
      T1 e;
    };

    using _frame = std::variant<_call, _after_map2_l_in_pair>;
    t<T3> _result{};
    crane::small_vector<_frame> _stack;
    _stack.emplace_back(_call{&m});
    while (!_stack.empty()) {
      _frame &_popped = _stack.back();
      if (std::holds_alternative<_call>(_popped)) {
        auto _f = std::move(std::get<_call>(_popped));
        _stack.pop_back();
        const List<std::pair<typename X::t, T1>> &m = *_f.m;
        if (std::holds_alternative<
                typename List<std::pair<typename X::t, T1>>::Nil>(m.v())) {
          _result = List<std::pair<typename X::t, T3>>::nil();
        } else {
          const auto &[a0, a1] = std::get<
              typename List<std::pair<typename X::t, T1>>::Cons>(m.v());
          const auto &[k, e] = a0;
          _stack.emplace_back(_after_map2_l_in_pair{k, e});
          _stack.emplace_back(_call{crane_raw(a1)});
        }
      } else {
        auto _f = std::move(std::get<_after_map2_l_in_pair>(_popped));
        _stack.pop_back();
        typename X::t k = std::move(_f.k);
        auto e = std::move(_f.e);
        _result = option_cons<T3>(
            std::move(k), f(std::make_optional<T1>(e), std::optional<T2>()),
            std::move(_result));
      }
    }
    return _result;
  }

  template <typename T1, typename T2, typename T3, typename F0>
  static t<T3> map2_r(F0 &&f, const List<std::pair<typename X::t, T2>> &m_) {
    // Explicit stack replaces the non-tail recursion of map2_r: _call frames
    // are pending calls, _after frames resume a caller.
    struct _call {
      const List<std::pair<typename X::t, T2>> *m_;
    };

    struct _after_map2_r_in_pair {
      typename X::t k;
      T2 e_;
    };

    using _frame = std::variant<_call, _after_map2_r_in_pair>;
    t<T3> _result{};
    crane::small_vector<_frame> _stack;
    _stack.emplace_back(_call{&m_});
    while (!_stack.empty()) {
      _frame &_popped = _stack.back();
      if (std::holds_alternative<_call>(_popped)) {
        auto _f = std::move(std::get<_call>(_popped));
        _stack.pop_back();
        const List<std::pair<typename X::t, T2>> &m_ = *_f.m_;
        if (std::holds_alternative<
                typename List<std::pair<typename X::t, T2>>::Nil>(m_.v())) {
          _result = List<std::pair<typename X::t, T3>>::nil();
        } else {
          const auto &[a0, a1] =
              std::get<typename List<std::pair<typename X::t, T2>>::Cons>(
                  m_.v());
          const auto &[k, e_] = a0;
          _stack.emplace_back(_after_map2_r_in_pair{k, e_});
          _stack.emplace_back(_call{crane_raw(a1)});
        }
      } else {
        auto _f = std::move(std::get<_after_map2_r_in_pair>(_popped));
        _stack.pop_back();
        typename X::t k = std::move(_f.k);
        auto e_ = std::move(_f.e_);
        _result = option_cons<T3>(
            std::move(k), f(std::optional<T1>(), std::make_optional<T2>(e_)),
            std::move(_result));
      }
    }
    return _result;
  }

  template <typename T1, typename T2, typename T3, typename F0>
  static t<T3> map2(F0 &&f, List<std::pair<typename X::t, T1>> m,
                    const t<T2> &x0_) {
    // Explicit stack replaces the non-tail recursion of map2: _call frames are
    // pending calls, _after frames resume a caller.
    struct _call {
      const t<T2> *x0_;
      List<std::pair<typename X::t, T1>> m;
    };

    struct _call_map2_aux {
      const List<std::pair<typename X::t, T2>> *m_;
      std::shared_ptr<List<std::pair<typename X::t, T1>>> a1;
      T1 e;
      std::decay_t<F0> f;
      typename X::t k;
      List<std::pair<typename X::t, T1>> m;
    };

    struct _after_map2_aux_in_GT {
      std::decay_t<F0> f;
      typename X::t k_;
      T2 e_;
    };

    struct _after_map2_in_EQ {
      std::decay_t<F0> f;
      T1 e;
      T2 e_;
      typename X::t k;
    };

    struct _after_map2_in_LT {
      std::decay_t<F0> f;
      T1 e;
      typename X::t k;
    };

    using _frame = std::variant<_call, _call_map2_aux, _after_map2_aux_in_GT,
                                _after_map2_in_EQ, _after_map2_in_LT>;
    t<T3> _result{};
    crane::small_vector<_frame> _stack;
    _stack.emplace_back(_call{&x0_, std::move(m)});
    while (!_stack.empty()) {
      _frame &_popped = _stack.back();
      if (std::holds_alternative<_call>(_popped)) {
        auto _f = std::move(std::get<_call>(_popped));
        _stack.pop_back();
        const t<T2> &x0_ = *_f.x0_;
        List<std::pair<typename X::t, T1>> m = std::move(_f.m);
        if (std::holds_alternative<
                typename List<std::pair<typename X::t, T1>>::Nil>(m.v_mut())) {
          _result = map2_r<T1, T2, T3>(f, std::move(x0_));
        } else {
          auto &[a0, a1] =
              std::get<typename List<std::pair<typename X::t, T1>>::Cons>(
                  m.v_mut());
          const auto &[k, e] = a0;
          _stack.emplace_back(_call_map2_aux{&x0_, a1, e, f, k, m});
        }
      } else if (std::holds_alternative<_call_map2_aux>(_popped)) {
        auto _f = std::move(std::get<_call_map2_aux>(_popped));
        _stack.pop_back();
        const List<std::pair<typename X::t, T2>> &m_ = *_f.m_;
        std::shared_ptr<List<std::pair<typename X::t, T1>>> a1 =
            std::move(_f.a1);
        auto e = std::move(_f.e);
        auto f = std::move(_f.f);
        typename X::t k = std::move(_f.k);
        List<std::pair<typename X::t, T1>> m = std::move(_f.m);
        if (std::holds_alternative<
                typename List<std::pair<typename X::t, T2>>::Nil>(m_.v())) {
          _result = map2_l<T1, T2, T3>(f, m);
        } else {
          const auto &[a00, a10] =
              std::get<typename List<std::pair<typename X::t, T2>>::Cons>(
                  m_.v());
          const auto &[k_, e_] = a00;
          auto &&_sv = X::compare(k, k_);
          if (std::holds_alternative<typename Compare<typename X::t>::LT>(
                  _sv.v())) {
            _stack.emplace_back(
                _after_map2_in_LT{f, std::move(e), std::move(k)});
            _stack.emplace_back(_call{&m_, *a1});
          } else if (
              std::holds_alternative<typename Compare<typename X::t>::EQ>(
                  _sv.v())) {
            _stack.emplace_back(
                _after_map2_in_EQ{f, std::move(e), e_, std::move(k)});
            _stack.emplace_back(_call{crane_raw(a10), *a1});
          } else {
            _stack.emplace_back(_after_map2_aux_in_GT{f, k_, e_});
            _stack.emplace_back(
                _call_map2_aux{crane_raw(a10), std::move(a1), std::move(e), f,
                               std::move(k), std::move(m)});
          }
        }
      } else if (std::holds_alternative<_after_map2_aux_in_GT>(_popped)) {
        auto _f = std::move(std::get<_after_map2_aux_in_GT>(_popped));
        _stack.pop_back();
        std::decay_t<F0> f = std::move(_f.f);
        typename X::t k_ = std::move(_f.k_);
        auto e_ = std::move(_f.e_);
        _result = option_cons<T3>(
            std::move(k_), f(std::optional<T1>(), std::make_optional<T2>(e_)),
            std::move(_result));
      } else if (std::holds_alternative<_after_map2_in_EQ>(_popped)) {
        auto _f = std::move(std::get<_after_map2_in_EQ>(_popped));
        _stack.pop_back();
        std::decay_t<F0> f = std::move(_f.f);
        auto e = std::move(_f.e);
        auto e_ = std::move(_f.e_);
        typename X::t k = std::move(_f.k);
        _result = option_cons<T3>(
            k, f(std::make_optional<T1>(e), std::make_optional<T2>(e_)),
            std::move(_result));
      } else {
        auto _f = std::move(std::get<_after_map2_in_LT>(_popped));
        _stack.pop_back();
        std::decay_t<F0> f = std::move(_f.f);
        auto e = std::move(_f.e);
        typename X::t k = std::move(_f.k);
        _result = option_cons<T3>(
            k, f(std::make_optional<T1>(e), std::optional<T2>()),
            std::move(_result));
      }
    }
    return _result;
  }

  template <typename T1, typename T2>
  static t<std::pair<std::optional<T1>, std::optional<T2>>>
  combine(List<std::pair<typename X::t, T1>> m, const t<T2> &x0_) {
    // Explicit stack replaces the non-tail recursion of combine: _call frames
    // are pending calls, _after frames resume a caller.
    struct _call {
      const t<T2> *x0_;
      List<std::pair<typename X::t, T1>> m;
    };

    struct _call_combine_aux {
      const List<std::pair<typename X::t, T2>> *m_;
      List<std::pair<typename X::t, T1>> a1_value;
      T1 e;
      typename X::t k;
      List<std::pair<typename X::t, T1>> m;
    };

    struct _after_combine_aux_in_GT {
      typename X::t k_;
      T2 e_;
    };

    struct _after_combine_in_EQ {
      T1 e;
      T2 e_;
      typename X::t k;
    };

    struct _after_combine_in_LT {
      T1 e;
      typename X::t k;
    };

    using _frame =
        std::variant<_call, _call_combine_aux, _after_combine_aux_in_GT,
                     _after_combine_in_EQ, _after_combine_in_LT>;
    t<std::pair<std::optional<T1>, std::optional<T2>>> _result{};
    crane::small_vector<_frame> _stack;
    _stack.emplace_back(_call{&x0_, std::move(m)});
    while (!_stack.empty()) {
      _frame &_popped = _stack.back();
      if (std::holds_alternative<_call>(_popped)) {
        auto _f = std::move(std::get<_call>(_popped));
        _stack.pop_back();
        const t<T2> &x0_ = *_f.x0_;
        List<std::pair<typename X::t, T1>> m = std::move(_f.m);
        if (std::holds_alternative<
                typename List<std::pair<typename X::t, T1>>::Nil>(m.v_mut())) {
          _result = map<T2, std::pair<std::optional<T1>, std::optional<T2>>>(
              [](const T2 &e_) {
                return std::make_pair(std::optional<T1>(),
                                      std::make_optional<T2>(e_));
              },
              std::move(x0_));
        } else {
          auto &[a0, a1] =
              std::get<typename List<std::pair<typename X::t, T1>>::Cons>(
                  m.v_mut());
          const List<std::pair<typename X::t, T1>> &a1_value = *a1;
          const auto &[k, e] = a0;
          _stack.emplace_back(_call_combine_aux{&x0_, a1_value, e, k, m});
        }
      } else if (std::holds_alternative<_call_combine_aux>(_popped)) {
        auto _f = std::move(std::get<_call_combine_aux>(_popped));
        _stack.pop_back();
        const List<std::pair<typename X::t, T2>> &m_ = *_f.m_;
        List<std::pair<typename X::t, T1>> a1_value = std::move(_f.a1_value);
        auto e = std::move(_f.e);
        typename X::t k = std::move(_f.k);
        List<std::pair<typename X::t, T1>> m = std::move(_f.m);
        if (std::holds_alternative<
                typename List<std::pair<typename X::t, T2>>::Nil>(m_.v())) {
          _result = map<T1, std::pair<std::optional<T1>, std::optional<T2>>>(
              [](const T1 &e0) {
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
            _stack.emplace_back(
                _after_combine_in_LT{std::move(e), std::move(k)});
            _stack.emplace_back(_call{&m_, std::move(a1_value)});
          } else if (
              std::holds_alternative<typename Compare<typename X::t>::EQ>(
                  _sv.v())) {
            _stack.emplace_back(
                _after_combine_in_EQ{std::move(e), e_, std::move(k)});
            _stack.emplace_back(_call{crane_raw(a10), std::move(a1_value)});
          } else {
            _stack.emplace_back(_after_combine_aux_in_GT{k_, e_});
            _stack.emplace_back(
                _call_combine_aux{crane_raw(a10), std::move(a1_value),
                                  std::move(e), std::move(k), std::move(m)});
          }
        }
      } else if (std::holds_alternative<_after_combine_aux_in_GT>(_popped)) {
        auto _f = std::move(std::get<_after_combine_aux_in_GT>(_popped));
        _stack.pop_back();
        typename X::t k_ = std::move(_f.k_);
        auto e_ = std::move(_f.e_);
        _result = List<std::pair<
            typename X::t,
            std::pair<std::optional<T1>, std::optional<T2>>>>::cons(
            std::make_pair(std::move(k_), std::make_pair(std::optional<T1>(),
                                                         std::make_optional<T2>(
                                                             std::move(e_)))),
            std::move(_result));
      } else if (std::holds_alternative<_after_combine_in_EQ>(_popped)) {
        auto _f = std::move(std::get<_after_combine_in_EQ>(_popped));
        _stack.pop_back();
        auto e = std::move(_f.e);
        auto e_ = std::move(_f.e_);
        typename X::t k = std::move(_f.k);
        _result = List<std::pair<
            typename X::t,
            std::pair<std::optional<T1>, std::optional<T2>>>>::cons(
            std::make_pair(
                k, std::make_pair(std::make_optional<T1>(e),
                                  std::make_optional<T2>(std::move(e_)))),
            std::move(_result));
      } else {
        auto _f = std::move(std::get<_after_combine_in_LT>(_popped));
        _stack.pop_back();
        auto e = std::move(_f.e);
        typename X::t k = std::move(_f.k);
        _result = List<std::pair<
            typename X::t,
            std::pair<std::optional<T1>, std::optional<T2>>>>::cons(
            std::make_pair(k, std::make_pair(std::make_optional<T1>(e),
                                             std::optional<T2>())),
            std::move(_result));
      }
    }
    return _result;
  }

  template <typename T1, typename T2, typename T3>
  static T3
  fold_right_pair(const std::type_identity_t<crane::fn<T3(T1, T2, T3)>> &f,
                  const List<std::pair<T1, T2>> &l, T3 i) {
    return l.template fold_right<T3>(
        [=, f = f](const std::pair<T1, T2> &p,
                   const T3 &eta0_) { return f(p.first, p.second, eta0_); },
        std::move(i));
  }

  template <typename T1, typename T2, typename T3>
  static List<std::pair<key, T3>>
  map2_alt(const std::type_identity_t<
      crane::fn<std::optional<T3>(std::optional<T1>, std::optional<T2>)>> &f,
           List<std::pair<typename X::t, T1>> m,
           const List<std::pair<typename X::t, T2>> &m_) {
    List<std::pair<typename X::t,
                   std::pair<std::optional<T1>, std::optional<T2>>>> m0 =
        combine<T1, T2>(std::move(m), m_);
    List<std::pair<typename X::t, std::optional<T3>>> m1 =
        map<std::pair<std::optional<T1>, std::optional<T2>>, std::optional<T3>>(
            [=, f = f](const std::pair<std::optional<T1>,
                                       std::optional<T2>> &p) {
              return f(p.first, p.second);
            },
            std::move(m0));
    return fold_right_pair<key, std::optional<T3>, List<std::pair<key, T3>>>(
        option_cons<T3>, std::move(m1), List<std::pair<key, T3>>::nil());
  }

  template <typename T1, typename T2>
  static std::optional<std::pair<std::optional<T1>, std::optional<T2>>>
  at_least_one(const std::optional<T1> &o, const std::optional<T2> &o_) {
    if (o.has_value()) {
      const T1 &_x = *o;
      return std::make_optional<std::pair<std::optional<T1>,
                                          std::optional<T2>>>(
          std::make_pair(o, o_));
    } else {
      if (o_.has_value()) {
        const T2 &_x = *o_;
        return std::make_optional<
            std::pair<std::optional<T1>, std::optional<T2>>>(
            std::make_pair(o, o_));
      } else {
        return std::optional<std::pair<std::optional<T1>, std::optional<T2>>>();
      }
    }
  }

  template <typename T1, typename T2, typename T3, typename F0>
  static std::optional<T3>
  at_least_one_then_f(F0 &&f, const std::optional<T1> &o,
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

struct Nat_as_OT {
  using t = uint64_t;
  static Compare<uint64_t> compare(uint64_t x, uint64_t y);
  static bool eq_dec(uint64_t x0_, uint64_t x1_);
};

template <typename M>
concept Int = requires {
  typename M::t;
  { M::i2z(std::declval<typename M::t>()) } -> std::same_as<Z>;
  requires (requires {
    {
      M::_0
    }
    -> std::convertible_to<typename M::t>;
  } || requires {
    {
      M::_0()
    }
    -> std::convertible_to<typename M::t>;
  });
  requires (requires {
    {
      M::_1
    }
    -> std::convertible_to<typename M::t>;
  } || requires {
    {
      M::_1()
    }
    -> std::convertible_to<typename M::t>;
  });
  requires (requires {
    {
      M::_2
    }
    -> std::convertible_to<typename M::t>;
  } || requires {
    {
      M::_2()
    }
    -> std::convertible_to<typename M::t>;
  });
  requires (requires {
    {
      M::_3
    }
    -> std::convertible_to<typename M::t>;
  } || requires {
    {
      M::_3()
    }
    -> std::convertible_to<typename M::t>;
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
  static Z max(Z x0_, Z x1_);
  static bool eqb(const Z &x0_, const Z &x1_);
  static bool ltb(const Z &x0_, const Z &x1_);
  static bool leb(const Z &x0_, const Z &x1_);
  static bool eq_dec(const Z &x0_, const Z &x1_);
  static bool gt_le_dec(const Z &i, const Z &j);
  static bool ge_lt_dec(const Z &i, const Z &j);
  static Z i2z(Z n);
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

    template <typename CraneU>
    tree(const tree<CraneU> &_other)
        : v_([&]() -> variant_t {
            if (std::holds_alternative<typename tree<CraneU>::Leaf>(_other.v())) {
              return Leaf{};
            } else {
              const auto &[a0, a1, a2, a3, a4] =
                  std::get<typename tree<CraneU>::Node>(_other.v());
              return Node{
                  (a0 ? std::make_shared<tree<elt>>(
                            crane_convert<tree<elt>>(*a0))
                      : nullptr),
                  a1,
                  [&]() -> elt {
                    if constexpr (crane_convertible<elt, const CraneU &>) {
                      return crane_convert<elt>(a2);
                    } else {
                      throw std::logic_error("unreachable: inactive "
                                             "constructor field at this "
                                             "instantiation");
                    }
                  }(),
                  (a3 ? std::make_shared<tree<elt>>(
                            crane_convert<tree<elt>>(*a3))
                      : nullptr),
                  a4};
            }
          }()) {}

    static tree<elt> leaf() { return tree<elt>(Leaf{}); }

    static tree<elt> node(crane::shared_child_slot<tree<elt>> a0, key a1,
                          elt a2, crane::shared_child_slot<tree<elt>> a3,
                          typename I::t a4) {
      return tree<elt>(Node{a0.take(), std::move(a1), std::move(a2), a3.take(),
                            std::move(a4)});
    }

    // MANIPULATORS
    ~tree() {
      // Release the children this node alone owns in a loop, not recursively,
      // so a deep value cannot overflow the stack.
      if (std::holds_alternative<Leaf>(v_mut())) {
        return;
      }
      if (auto *_alt = std::get_if<Node>(&v_mut())) {
        if (!((_alt->a0 && _alt->a0.use_count() == 1) ||
              (_alt->a3 && _alt->a3.use_count() == 1))) {
          return;
        }
      }
      crane::small_vector<std::shared_ptr<tree<elt>>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<Node>(&_v)) {
          if (_alt->a0 && _alt->a0.use_count() == 1) {
            _stack.push_back(std::move(_alt->a0));
          }
          if (_alt->a3 && _alt->a3.use_count() == 1) {
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
    tree(tree &&) = default;
    tree &operator=(tree &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename T2, typename F1>
  static T2 tree_rect(T2 f, F1 &&f0, const tree<T1> &t0) {
    // Explicit stack replaces the non-tail recursion of tree_rect: _call frames
    // are pending calls, _after frames resume a caller.
    struct _call {
      const tree<T1> *t0;
    };

    struct _after_tree_rect_in_Node {
      std::shared_ptr<tree<T1>> a0;
      typename X::t a1;
      T1 a2;
      const tree<T1> *a3;
      typename I::t a4;
    };

    struct _after_tree_rect_in_Node_2 {
      std::shared_ptr<tree<T1>> a0;
      typename X::t a1;
      T1 a2;
      const tree<T1> *a3;
      typename I::t a4;
      T2 _tmp2;
    };

    using _frame = std::variant<_call, _after_tree_rect_in_Node,
                                _after_tree_rect_in_Node_2>;
    T2 _result{};
    crane::small_vector<_frame> _stack;
    _stack.emplace_back(_call{&t0});
    while (!_stack.empty()) {
      _frame &_popped = _stack.back();
      if (std::holds_alternative<_call>(_popped)) {
        auto _f = std::move(std::get<_call>(_popped));
        _stack.pop_back();
        const tree<T1> &t0 = *_f.t0;
        if (std::holds_alternative<typename tree<T1>::Leaf>(t0.v())) {
          _result = f;
        } else {
          const auto &[a0, a1, a2, a3, a4] =
              std::get<typename tree<T1>::Node>(t0.v());
          _stack.emplace_back(
              _after_tree_rect_in_Node{a0, a1, a2, crane_raw(a3), a4});
          _stack.emplace_back(_call{crane_raw(a0)});
        }
      } else if (std::holds_alternative<_after_tree_rect_in_Node>(_popped)) {
        auto _f = std::move(std::get<_after_tree_rect_in_Node>(_popped));
        _stack.pop_back();
        std::shared_ptr<tree<T1>> a0 = std::move(_f.a0);
        typename X::t a1 = std::move(_f.a1);
        auto a2 = std::move(_f.a2);
        const tree<T1> &a3 = *_f.a3;
        typename I::t a4 = std::move(_f.a4);
        _stack.emplace_back(_after_tree_rect_in_Node_2{
            std::move(a0), std::move(a1), std::move(a2), &a3, std::move(a4),
            std::move(_result)});
        _stack.emplace_back(_call{&a3});
      } else {
        auto _f = std::move(std::get<_after_tree_rect_in_Node_2>(_popped));
        _stack.pop_back();
        std::shared_ptr<tree<T1>> a0 = std::move(_f.a0);
        typename X::t a1 = std::move(_f.a1);
        auto a2 = std::move(_f.a2);
        const tree<T1> &a3 = *_f.a3;
        typename I::t a4 = std::move(_f.a4);
        _result =
            f0(*a0, std::move(_f._tmp2), a1, a2, a3, std::move(_result), a4);
      }
    }
    return _result;
  }

  template <typename T1, typename T2, typename F1>
  static T2 tree_rec(T2 f, F1 &&f0, const tree<T1> &t0) {
    return tree_rect<T1, T2>(std::move(f), f0, t0);
  }

  template <typename T1> static typename I::t height(const tree<T1> &m) {
    if (std::holds_alternative<typename tree<T1>::Leaf>(m.v())) {
      return I::_0;
    } else {
      const auto &[_, _, _, _, a4] = std::get<typename tree<T1>::Node>(m.v());
      return a4;
    }
  }

  template <typename T1> static uint64_t cardinal(const tree<T1> &m) {
    // Explicit stack replaces the non-tail recursion of cardinal: _call frames
    // are pending calls, _after frames resume a caller.
    struct _call {
      const tree<T1> *m;
    };

    struct _after_cardinal_in_Node {
      const tree<T1> *a3;
    };

    struct _after_cardinal_in_Node_2 {
      uint64_t _tmp2;
    };

    using _frame =
        std::variant<_call, _after_cardinal_in_Node, _after_cardinal_in_Node_2>;
    uint64_t _result{};
    crane::small_vector<_frame> _stack;
    _stack.emplace_back(_call{&m});
    while (!_stack.empty()) {
      _frame &_popped = _stack.back();
      if (std::holds_alternative<_call>(_popped)) {
        auto _f = std::move(std::get<_call>(_popped));
        _stack.pop_back();
        const tree<T1> &m = *_f.m;
        if (std::holds_alternative<typename tree<T1>::Leaf>(m.v())) {
          _result = UINT64_C(0);
        } else {
          const auto &[a0, _, _, a3, _] =
              std::get<typename tree<T1>::Node>(m.v());
          _stack.emplace_back(_after_cardinal_in_Node{crane_raw(a3)});
          _stack.emplace_back(_call{crane_raw(a0)});
        }
      } else if (std::holds_alternative<_after_cardinal_in_Node>(_popped)) {
        auto _f = std::move(std::get<_after_cardinal_in_Node>(_popped));
        _stack.pop_back();
        const tree<T1> &a3 = *_f.a3;
        _stack.emplace_back(_after_cardinal_in_Node_2{_result});
        _stack.emplace_back(_call{&a3});
      } else {
        auto _f = std::move(std::get<_after_cardinal_in_Node_2>(_popped));
        _stack.pop_back();
        _result = ((_f._tmp2 + _result) + 1);
      }
    }
    return _result;
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
    // Loop replaces the tail recursion: each recursive call updates the loop
    // variables.
    const tree<T1> *_loop_m = &m;
    while (true) {
      if (std::holds_alternative<typename tree<T1>::Leaf>(_loop_m->v())) {
        return false;
      } else {
        const auto &[a0, a1, _, a3, _] =
            std::get<typename tree<T1>::Node>(_loop_m->v());
        auto &&_sv = X::compare(x, a1);
        if (std::holds_alternative<typename Compare<typename X::t>::LT>(_sv.v())) {
          _loop_m = crane_raw(a0);
        } else if (std::holds_alternative<typename Compare<typename X::t>::EQ>(
                       _sv.v())) {
          return true;
        } else {
          _loop_m = crane_raw(a3);
        }
      }
    }
  }

  template <typename T1>
  static std::optional<T1> find(typename X::t x, const tree<T1> &m) {
    // Loop replaces the tail recursion: each recursive call updates the loop
    // variables.
    const tree<T1> *_loop_m = &m;
    while (true) {
      if (std::holds_alternative<typename tree<T1>::Leaf>(_loop_m->v())) {
        return std::optional<T1>();
      } else {
        const auto &[a0, a1, a2, a3, _] =
            std::get<typename tree<T1>::Node>(_loop_m->v());
        auto &&_sv = X::compare(x, a1);
        if (std::holds_alternative<typename Compare<typename X::t>::LT>(_sv.v())) {
          _loop_m = crane_raw(a0);
        } else if (std::holds_alternative<typename Compare<typename X::t>::EQ>(
                       _sv.v())) {
          return std::make_optional<T1>(a2);
        } else {
          _loop_m = crane_raw(a3);
        }
      }
    }
  }

  template <typename T1>
  static tree<T1> create(const tree<T1> &l, typename X::t x, const T1 &e,
                         const tree<T1> &r) {
    return tree<T1>::node(l, std::move(x), e, r,
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
        const auto &[a0, a1, a2, a3, _] =
            std::get<typename tree<T1>::Node>(l.v());
        if (I::ge_lt_dec(height<T1>(*a0), height<T1>(*a3))) {
          return create<T1>(*a0, a1, a2, create<T1>(*a3, std::move(x), d, r));
        } else {
          auto &&_sv0 = *a3;
          if (std::holds_alternative<typename tree<T1>::Leaf>(_sv0.v())) {
            return assert_false<T1>(l, std::move(x), d, r);
          } else {
            const auto &[a00, a10, a20, a30, _] =
                std::get<typename tree<T1>::Node>(_sv0.v());
            return create<T1>(create<T1>(*a0, a1, a2, *a00), a10, a20,
                              create<T1>(*a30, std::move(x), d, r));
          }
        }
      }
    } else if (I::gt_le_dec(std::move(hr), I::add(std::move(hl), I::_2))) {
      if (std::holds_alternative<typename tree<T1>::Leaf>(r.v())) {
        return assert_false<T1>(l, std::move(x), d, r);
      } else {
        const auto &[a00, a10, a20, a30, _] =
            std::get<typename tree<T1>::Node>(r.v());
        if (I::ge_lt_dec(height<T1>(*a30), height<T1>(*a00))) {
          return create<T1>(create<T1>(l, std::move(x), d, *a00), a10, a20,
                            *a30);
        } else {
          auto &&_sv1 = *a00;
          if (std::holds_alternative<typename tree<T1>::Leaf>(_sv1.v())) {
            return assert_false<T1>(l, std::move(x), d, r);
          } else {
            const auto &[a01, a11, a21, a31, _] =
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

  template <typename T1>
  static tree<T1> add(typename X::t x, const T1 &d, const tree<T1> &m) {
    // Explicit stack replaces the non-tail recursion of add: _call frames are
    // pending calls, _after frames resume a caller.
    struct _call {
      const tree<T1> *m;
    };

    struct _after_add_in_GT {
      std::shared_ptr<tree<T1>> a0;
      typename X::t a1;
      T1 a2;
    };

    struct _after_add_in_LT {
      typename X::t a1;
      T1 a2;
      std::shared_ptr<tree<T1>> a3;
    };

    using _frame = std::variant<_call, _after_add_in_GT, _after_add_in_LT>;
    tree<T1> _result{};
    crane::small_vector<_frame> _stack;
    _stack.emplace_back(_call{&m});
    while (!_stack.empty()) {
      _frame &_popped = _stack.back();
      if (std::holds_alternative<_call>(_popped)) {
        auto _f = std::move(std::get<_call>(_popped));
        _stack.pop_back();
        const tree<T1> &m = *_f.m;
        if (std::holds_alternative<typename tree<T1>::Leaf>(m.v())) {
          _result =
              tree<T1>::node(tree<T1>::leaf(), x, d, tree<T1>::leaf(), I::_1);
        } else {
          const auto &[a0, a1, a2, a3, a4] =
              std::get<typename tree<T1>::Node>(m.v());
          auto &&_sv = X::compare(x, a1);
          if (std::holds_alternative<typename Compare<typename X::t>::LT>(
                  _sv.v())) {
            _stack.emplace_back(_after_add_in_LT{a1, a2, a3});
            _stack.emplace_back(_call{crane_raw(a0)});
          } else if (
              std::holds_alternative<typename Compare<typename X::t>::EQ>(
                  _sv.v())) {
            _result = tree<T1>::node(crane::shared_child(a0), a1, d,
                                     crane::shared_child(a3), a4);
          } else {
            _stack.emplace_back(_after_add_in_GT{a0, a1, a2});
            _stack.emplace_back(_call{crane_raw(a3)});
          }
        }
      } else if (std::holds_alternative<_after_add_in_GT>(_popped)) {
        auto _f = std::move(std::get<_after_add_in_GT>(_popped));
        _stack.pop_back();
        std::shared_ptr<tree<T1>> a0 = std::move(_f.a0);
        typename X::t a1 = std::move(_f.a1);
        auto a2 = std::move(_f.a2);
        _result =
            bal<T1>(*a0, std::move(a1), std::move(a2), std::move(_result));
      } else {
        auto _f = std::move(std::get<_after_add_in_LT>(_popped));
        _stack.pop_back();
        typename X::t a1 = std::move(_f.a1);
        auto a2 = std::move(_f.a2);
        std::shared_ptr<tree<T1>> a3 = std::move(_f.a3);
        _result =
            bal<T1>(std::move(_result), std::move(a1), std::move(a2), *a3);
      }
    }
    return _result;
  }

  template <typename T1>
  static std::pair<tree<T1>, std::pair<key, T1>>
  remove_min(const tree<T1> &l, typename X::t x, const T1 &d,
             const tree<T1> &r) {
    // Explicit stack replaces the non-tail recursion of remove_min: _call
    // frames are pending calls, _after frames resume a caller.
    struct _call {
      const tree<T1> *r;
      T1 d;
      typename X::t x;
      const tree<T1> *l;
    };

    struct _after_remove_min_in_Node {
      typename X::t x;
      T1 d;
      tree<T1> r;
    };

    using _frame = std::variant<_call, _after_remove_min_in_Node>;
    std::pair<tree<T1>, std::pair<key, T1>> _result{};
    crane::small_vector<_frame> _stack;
    _stack.emplace_back(_call{&r, d, std::move(x), &l});
    while (!_stack.empty()) {
      _frame &_popped = _stack.back();
      if (std::holds_alternative<_call>(_popped)) {
        auto _f = std::move(std::get<_call>(_popped));
        _stack.pop_back();
        const tree<T1> &r = *_f.r;
        const T1 d = std::move(_f.d);
        typename X::t x = std::move(_f.x);
        const tree<T1> &l = *_f.l;
        if (std::holds_alternative<typename tree<T1>::Leaf>(l.v())) {
          _result =
              std::make_pair(r, std::make_pair(std::move(x), std::move(d)));
        } else {
          const auto &[a0, a1, a2, a3, _] =
              std::get<typename tree<T1>::Node>(l.v());
          _stack.emplace_back(_after_remove_min_in_Node{std::move(x), d, r});
          _stack.emplace_back(_call{crane_raw(a3), a2, a1, crane_raw(a0)});
        }
      } else {
        auto _f = std::move(std::get<_after_remove_min_in_Node>(_popped));
        _stack.pop_back();
        typename X::t x = std::move(_f.x);
        const T1 d = std::move(_f.d);
        tree<T1> r = std::move(_f.r);
        auto [l_, m] = std::move(_result);
        _result = std::make_pair(
            bal<T1>(std::move(l_), std::move(x), std::move(d), std::move(r)),
            std::move(m));
      }
    }
    return _result;
  }

  template <typename T1>
  static tree<T1> merge(const tree<T1> &s1, const tree<T1> &s2) {
    if (std::holds_alternative<typename tree<T1>::Leaf>(s1.v())) {
      return s2;
    } else {
      if (std::holds_alternative<typename tree<T1>::Leaf>(s2.v())) {
        return s1;
      } else {
        const auto &[a00, a10, a20, a30, _] =
            std::get<typename tree<T1>::Node>(s2.v());
        auto [s2_, p] = remove_min<T1>(*a00, a10, a20, *a30);
        auto [x, d] = std::move(p);
        return bal<T1>(s1, std::move(x), std::move(d), std::move(s2_));
      }
    }
  }

  template <typename T1>
  static tree<T1> remove(typename X::t x, const tree<T1> &m) {
    // Explicit stack replaces the non-tail recursion of remove: _call frames
    // are pending calls, _after frames resume a caller.
    struct _call {
      const tree<T1> *m;
    };

    struct _after_remove_in_GT {
      std::shared_ptr<tree<T1>> a0;
      typename X::t a1;
      T1 a2;
    };

    struct _after_remove_in_LT {
      typename X::t a1;
      T1 a2;
      std::shared_ptr<tree<T1>> a3;
    };

    using _frame =
        std::variant<_call, _after_remove_in_GT, _after_remove_in_LT>;
    tree<T1> _result{};
    crane::small_vector<_frame> _stack;
    _stack.emplace_back(_call{&m});
    while (!_stack.empty()) {
      _frame &_popped = _stack.back();
      if (std::holds_alternative<_call>(_popped)) {
        auto _f = std::move(std::get<_call>(_popped));
        _stack.pop_back();
        const tree<T1> &m = *_f.m;
        if (std::holds_alternative<typename tree<T1>::Leaf>(m.v())) {
          _result = tree<T1>::leaf();
        } else {
          const auto &[a0, a1, a2, a3, _] =
              std::get<typename tree<T1>::Node>(m.v());
          auto &&_sv = X::compare(x, a1);
          if (std::holds_alternative<typename Compare<typename X::t>::LT>(
                  _sv.v())) {
            _stack.emplace_back(_after_remove_in_LT{a1, a2, a3});
            _stack.emplace_back(_call{crane_raw(a0)});
          } else if (
              std::holds_alternative<typename Compare<typename X::t>::EQ>(
                  _sv.v())) {
            _result = merge<T1>(*a0, *a3);
          } else {
            _stack.emplace_back(_after_remove_in_GT{a0, a1, a2});
            _stack.emplace_back(_call{crane_raw(a3)});
          }
        }
      } else if (std::holds_alternative<_after_remove_in_GT>(_popped)) {
        auto _f = std::move(std::get<_after_remove_in_GT>(_popped));
        _stack.pop_back();
        std::shared_ptr<tree<T1>> a0 = std::move(_f.a0);
        typename X::t a1 = std::move(_f.a1);
        auto a2 = std::move(_f.a2);
        _result =
            bal<T1>(*a0, std::move(a1), std::move(a2), std::move(_result));
      } else {
        auto _f = std::move(std::get<_after_remove_in_LT>(_popped));
        _stack.pop_back();
        typename X::t a1 = std::move(_f.a1);
        auto a2 = std::move(_f.a2);
        std::shared_ptr<tree<T1>> a3 = std::move(_f.a3);
        _result =
            bal<T1>(std::move(_result), std::move(a1), std::move(a2), *a3);
      }
    }
    return _result;
  }

  template <typename T1>
  static tree<T1> join(tree<T1> l, key x0_, T1 x1_, const tree<T1> &x2_) {
    // Explicit stack replaces the non-tail recursion of join: _call frames are
    // pending calls, _after frames resume a caller.
    struct _call {
      const tree<T1> *x2_;
      tree<T1> l;
    };

    struct _call_join_aux {
      const tree<T1> *r;
      std::shared_ptr<tree<T1>> a0;
      typename X::t a1;
      T1 a2;
      std::shared_ptr<tree<T1>> a3;
      typename I::t a4;
      tree<T1> l;
      key x0_;
      T1 x1_;
    };

    struct _after_join_aux_in_left {
      typename X::t a10;
      T1 a20;
      std::shared_ptr<tree<T1>> a30;
    };

    struct _after_join_in_left {
      std::shared_ptr<tree<T1>> a0;
      typename X::t a1;
      T1 a2;
    };

    using _frame = std::variant<_call, _call_join_aux, _after_join_aux_in_left,
                                _after_join_in_left>;
    tree<T1> _result{};
    crane::small_vector<_frame> _stack;
    _stack.emplace_back(_call{&x2_, std::move(l)});
    while (!_stack.empty()) {
      _frame &_popped = _stack.back();
      if (std::holds_alternative<_call>(_popped)) {
        auto _f = std::move(std::get<_call>(_popped));
        _stack.pop_back();
        const tree<T1> &x2_ = *_f.x2_;
        tree<T1> l = std::move(_f.l);
        if (std::holds_alternative<typename tree<T1>::Leaf>(l.v_mut())) {
          _result = add<T1>(x0_, x1_, std::move(x2_));
        } else {
          auto &[a0, a1, a2, a3, a4] =
              std::get<typename tree<T1>::Node>(l.v_mut());
          _stack.emplace_back(
              _call_join_aux{&x2_, a0, a1, a2, a3, a4, l, x0_, x1_});
        }
      } else if (std::holds_alternative<_call_join_aux>(_popped)) {
        auto _f = std::move(std::get<_call_join_aux>(_popped));
        _stack.pop_back();
        const tree<T1> &r = *_f.r;
        std::shared_ptr<tree<T1>> a0 = std::move(_f.a0);
        typename X::t a1 = std::move(_f.a1);
        auto a2 = std::move(_f.a2);
        std::shared_ptr<tree<T1>> a3 = std::move(_f.a3);
        typename I::t a4 = std::move(_f.a4);
        tree<T1> l = std::move(_f.l);
        key x0_ = std::move(_f.x0_);
        auto x1_ = std::move(_f.x1_);
        if (std::holds_alternative<typename tree<T1>::Leaf>(r.v())) {
          _result = add<T1>(x0_, x1_, l);
        } else {
          const auto &[a00, a10, a20, a30, a40] =
              std::get<typename tree<T1>::Node>(r.v());
          if (I::gt_le_dec(a4, I::add(a40, I::_2))) {
            _stack.emplace_back(_after_join_in_left{
                std::move(a0), std::move(a1), std::move(a2)});
            _stack.emplace_back(_call{&r, *a3});
          } else if (I::gt_le_dec(a40, I::add(a4, I::_2))) {
            _stack.emplace_back(_after_join_aux_in_left{a10, a20, a30});
            _stack.emplace_back(_call_join_aux{
                crane_raw(a00), std::move(a0), std::move(a1), std::move(a2),
                std::move(a3), std::move(a4), std::move(l), x0_, x1_});
          } else {
            _result = create<T1>(l, x0_, x1_, r);
          }
        }
      } else if (std::holds_alternative<_after_join_aux_in_left>(_popped)) {
        auto _f = std::move(std::get<_after_join_aux_in_left>(_popped));
        _stack.pop_back();
        typename X::t a10 = std::move(_f.a10);
        auto a20 = std::move(_f.a20);
        std::shared_ptr<tree<T1>> a30 = std::move(_f.a30);
        _result =
            bal<T1>(std::move(_result), std::move(a10), std::move(a20), *a30);
      } else {
        auto _f = std::move(std::get<_after_join_in_left>(_popped));
        _stack.pop_back();
        std::shared_ptr<tree<T1>> a0 = std::move(_f.a0);
        typename X::t a1 = std::move(_f.a1);
        auto a2 = std::move(_f.a2);
        _result = bal<T1>(*a0, a1, a2, std::move(_result));
      }
    }
    return _result;
  }

  template <typename elt> struct triple {
    tree<elt> t_left;
    std::optional<elt> t_opt;
    tree<elt> t_right;

    // ACCESSORS
    template <typename CraneU> operator triple<CraneU>() const {
      return {crane_convert<tree<CraneU>>(t_left), std::optional<CraneU>(t_opt),
              crane_convert<tree<CraneU>>(t_right)};
    }
  };

  template <typename T1>
  static triple<T1> split(typename X::t x, const tree<T1> &m) {
    // Explicit stack replaces the non-tail recursion of split: _call frames are
    // pending calls, _after frames resume a caller.
    struct _call {
      const tree<T1> *m;
    };

    struct _after_split_in_GT {
      std::shared_ptr<tree<T1>> a0;
      typename X::t a1;
      T1 a2;
    };

    struct _after_split_in_LT {
      typename X::t a1;
      T1 a2;
      std::shared_ptr<tree<T1>> a3;
    };

    using _frame = std::variant<_call, _after_split_in_GT, _after_split_in_LT>;
    triple<T1> _result{};
    crane::small_vector<_frame> _stack;
    _stack.emplace_back(_call{&m});
    while (!_stack.empty()) {
      _frame &_popped = _stack.back();
      if (std::holds_alternative<_call>(_popped)) {
        auto _f = std::move(std::get<_call>(_popped));
        _stack.pop_back();
        const tree<T1> &m = *_f.m;
        if (std::holds_alternative<typename tree<T1>::Leaf>(m.v())) {
          _result = triple<T1>{tree<T1>::leaf(), std::optional<T1>(),
                               tree<T1>::leaf()};
        } else {
          const auto &[a0, a1, a2, a3, _] =
              std::get<typename tree<T1>::Node>(m.v());
          auto &&_sv = X::compare(x, a1);
          if (std::holds_alternative<typename Compare<typename X::t>::LT>(
                  _sv.v())) {
            _stack.emplace_back(_after_split_in_LT{a1, a2, a3});
            _stack.emplace_back(_call{crane_raw(a0)});
          } else if (
              std::holds_alternative<typename Compare<typename X::t>::EQ>(
                  _sv.v())) {
            _result = triple<T1>{*a0, std::make_optional<T1>(a2), *a3};
          } else {
            _stack.emplace_back(_after_split_in_GT{a0, a1, a2});
            _stack.emplace_back(_call{crane_raw(a3)});
          }
        }
      } else if (std::holds_alternative<_after_split_in_GT>(_popped)) {
        auto _f = std::move(std::get<_after_split_in_GT>(_popped));
        _stack.pop_back();
        std::shared_ptr<tree<T1>> a0 = std::move(_f.a0);
        typename X::t a1 = std::move(_f.a1);
        auto a2 = std::move(_f.a2);
        auto _cs = std::move(_result);
        tree<T1> rl = std::move(_cs).t_left;
        std::optional<T1> o = std::move(_cs).t_opt;
        tree<T1> rr = std::move(_cs).t_right;
        _result = triple<T1>{
            join<T1>(*a0, std::move(a1), std::move(a2), std::move(rl)),
            std::move(o), std::move(rr)};
      } else {
        auto _f = std::move(std::get<_after_split_in_LT>(_popped));
        _stack.pop_back();
        typename X::t a1 = std::move(_f.a1);
        auto a2 = std::move(_f.a2);
        std::shared_ptr<tree<T1>> a3 = std::move(_f.a3);
        auto _cs = std::move(_result);
        tree<T1> ll = std::move(_cs).t_left;
        std::optional<T1> o = std::move(_cs).t_opt;
        tree<T1> rl = std::move(_cs).t_right;
        _result = triple<T1>{
            std::move(ll), std::move(o),
            join<T1>(std::move(rl), std::move(a1), std::move(a2), *a3)};
      }
    }
    return _result;
  }

  template <typename T1>
  static tree<T1> concat(tree<T1> m1, const tree<T1> &m2) {
    if (std::holds_alternative<typename tree<T1>::Leaf>(m1.v())) {
      return m2;
    } else {
      if (std::holds_alternative<typename tree<T1>::Leaf>(m2.v())) {
        return m1;
      } else {
        const auto &[a00, a10, a20, a30, _] =
            std::get<typename tree<T1>::Node>(m2.v());
        auto [m2_, xd] = remove_min<T1>(*a00, a10, a20, *a30);
        return join<T1>(m1, std::move(xd).first, std::move(xd).second,
                        std::move(m2_));
      }
    }
  }

  template <typename T1>
  static List<std::pair<key, T1>>
  elements_aux(List<std::pair<typename X::t, T1>> acc, const tree<T1> &m) {
    // Explicit stack replaces the non-tail recursion of elements_aux: _call
    // frames are pending calls, _after frames resume a caller.
    struct _call {
      const tree<T1> *m;
      List<std::pair<typename X::t, T1>> acc;
    };

    struct _after_elements_aux_in_Node {
      const tree<T1> *a0;
      typename X::t a1;
      T1 a2;
    };

    using _frame = std::variant<_call, _after_elements_aux_in_Node>;
    List<std::pair<key, T1>> _result{};
    crane::small_vector<_frame> _stack;
    _stack.emplace_back(_call{&m, std::move(acc)});
    while (!_stack.empty()) {
      _frame &_popped = _stack.back();
      if (std::holds_alternative<_call>(_popped)) {
        auto _f = std::move(std::get<_call>(_popped));
        _stack.pop_back();
        const tree<T1> &m = *_f.m;
        List<std::pair<typename X::t, T1>> acc = std::move(_f.acc);
        if (std::holds_alternative<typename tree<T1>::Leaf>(m.v())) {
          _result = std::move(acc);
        } else {
          const auto &[a0, a1, a2, a3, _] =
              std::get<typename tree<T1>::Node>(m.v());
          _stack.emplace_back(
              _after_elements_aux_in_Node{crane_raw(a0), a1, a2});
          _stack.emplace_back(_call{crane_raw(a3), std::move(acc)});
        }
      } else {
        auto _f = std::move(std::get<_after_elements_aux_in_Node>(_popped));
        _stack.pop_back();
        const tree<T1> &a0 = *_f.a0;
        typename X::t a1 = std::move(_f.a1);
        auto a2 = std::move(_f.a2);
        _stack.emplace_back(
            _call{&a0, List<std::pair<typename X::t, T1>>::cons(
                           std::make_pair(std::move(a1), std::move(a2)),
                           std::move(_result))});
      }
    }
    return _result;
  }

  template <typename T1>
  static List<std::pair<key, T1>> elements(const tree<T1> &m) {
    return elements_aux<T1>(List<std::pair<key, T1>>::nil(), m);
  }

  template <typename T1, typename T2, typename F0>
    requires std::is_invocable_r_v<T2, F0 &, typename X::t &, T1 &, T2 &&>
  static T2 fold(F0 &&f, const tree<T1> &m, T2 a) {
    // Explicit stack replaces the non-tail recursion of fold: _call frames are
    // pending calls, _after frames resume a caller.
    struct _call {
      T2 a;
      const tree<T1> *m;
    };

    struct _after_fold_in_Node {
      typename X::t a1;
      T1 a2;
      const tree<T1> *a3;
    };

    using _frame = std::variant<_call, _after_fold_in_Node>;
    T2 _result{};
    crane::small_vector<_frame> _stack;
    _stack.emplace_back(_call{std::move(a), &m});
    while (!_stack.empty()) {
      _frame &_popped = _stack.back();
      if (std::holds_alternative<_call>(_popped)) {
        auto _f = std::move(std::get<_call>(_popped));
        _stack.pop_back();
        auto a = std::move(_f.a);
        const tree<T1> &m = *_f.m;
        if (std::holds_alternative<typename tree<T1>::Leaf>(m.v())) {
          _result = std::move(a);
        } else {
          const auto &[a0, a1, a2, a3, _] =
              std::get<typename tree<T1>::Node>(m.v());
          _stack.emplace_back(_after_fold_in_Node{a1, a2, crane_raw(a3)});
          _stack.emplace_back(_call{std::move(a), crane_raw(a0)});
        }
      } else {
        auto _f = std::move(std::get<_after_fold_in_Node>(_popped));
        _stack.pop_back();
        typename X::t a1 = std::move(_f.a1);
        auto a2 = std::move(_f.a2);
        const tree<T1> &a3 = *_f.a3;
        _stack.emplace_back(_call{f(a1, a2, std::move(_result)), &a3});
      }
    }
    return _result;
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

    template <typename CraneU>
    enumeration(const enumeration<CraneU> &_other)
        : v_([&]() -> variant_t {
            if (std::holds_alternative<typename enumeration<CraneU>::End>(
                    _other.v())) {
              return End{};
            } else {
              const auto &[a0, a1, a2, a3] =
                  std::get<typename enumeration<CraneU>::More>(_other.v());
              return More{
                  a0,
                  [&]() -> elt {
                    if constexpr (crane_convertible<elt, const CraneU &>) {
                      return crane_convert<elt>(a1);
                    } else {
                      throw std::logic_error("unreachable: inactive "
                                             "constructor field at this "
                                             "instantiation");
                    }
                  }(),
                  crane_convert<tree<elt>>(a2),
                  (a3 ? std::make_shared<enumeration<elt>>(
                            crane_convert<enumeration<elt>>(*a3))
                      : nullptr)};
            }
          }()) {}

    static enumeration<elt> end() { return enumeration<elt>(End{}); }

    static enumeration<elt>
    more(key a0, elt a1, tree<elt> a2,
         crane::shared_child_slot<enumeration<elt>> a3) {
      return enumeration<elt>(
          More{std::move(a0), std::move(a1), std::move(a2), a3.take()});
    }

    // MANIPULATORS
    ~enumeration() {
      // Release the children this node alone owns in a loop, not recursively,
      // so a deep value cannot overflow the stack.
      auto _next = [&](variant_t &_v) -> std::shared_ptr<enumeration<elt>> {
        if (auto *_alt = std::get_if<More>(&_v)) {
          if (_alt->a3 && _alt->a3.use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            return std::move(_alt->a3);
          }
        }
        return nullptr;
      };
      std::shared_ptr<enumeration<elt>> _cur = _next(v_mut());
      while (_cur) {
        _cur = _next(_cur->v_mut());
      }
    }

    enumeration(const enumeration &) = default;
    enumeration &operator=(const enumeration &) = default;
    enumeration(enumeration &&) = default;
    enumeration &operator=(enumeration &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename T2, typename F1>
  static T2 enumeration_rect(T2 f, F1 &&f0, const enumeration<T1> &e) {
    // Explicit stack replaces the non-tail recursion of enumeration_rect: _call
    // frames are pending calls, _after frames resume a caller.
    struct _call {
      const enumeration<T1> *e;
    };

    struct _after_enumeration_rect_in_More {
      typename X::t a0;
      T1 a1;
      tree<T1> a2;
      std::shared_ptr<enumeration<T1>> a3;
    };

    using _frame = std::variant<_call, _after_enumeration_rect_in_More>;
    T2 _result{};
    crane::small_vector<_frame> _stack;
    _stack.emplace_back(_call{&e});
    while (!_stack.empty()) {
      _frame &_popped = _stack.back();
      if (std::holds_alternative<_call>(_popped)) {
        auto _f = std::move(std::get<_call>(_popped));
        _stack.pop_back();
        const enumeration<T1> &e = *_f.e;
        if (std::holds_alternative<typename enumeration<T1>::End>(e.v())) {
          _result = f;
        } else {
          const auto &[a0, a1, a2, a3] =
              std::get<typename enumeration<T1>::More>(e.v());
          _stack.emplace_back(_after_enumeration_rect_in_More{a0, a1, a2, a3});
          _stack.emplace_back(_call{crane_raw(a3)});
        }
      } else {
        auto _f = std::move(std::get<_after_enumeration_rect_in_More>(_popped));
        _stack.pop_back();
        typename X::t a0 = std::move(_f.a0);
        auto a1 = std::move(_f.a1);
        tree<T1> a2 = std::move(_f.a2);
        std::shared_ptr<enumeration<T1>> a3 = std::move(_f.a3);
        _result = f0(a0, a1, a2, *a3, std::move(_result));
      }
    }
    return _result;
  }

  template <typename T1, typename T2, typename F1>
  static T2 enumeration_rec(T2 f, F1 &&f0, const enumeration<T1> &e) {
    return enumeration_rect<T1, T2>(std::move(f), f0, e);
  }

  template <typename T1>
  static enumeration<T1> cons(const tree<T1> &m, enumeration<T1> e) {
    // Loop replaces the tail recursion: each recursive call updates the loop
    // variables.
    enumeration<T1> _loop_e = std::move(e);
    const tree<T1> *_loop_m = &m;
    while (true) {
      if (std::holds_alternative<typename tree<T1>::Leaf>(_loop_m->v())) {
        return _loop_e;
      } else {
        const auto &[a0, a1, a2, a3, _] =
            std::get<typename tree<T1>::Node>(_loop_m->v());
        _loop_e = enumeration<T1>::more(a1, a2, *a3, std::move(_loop_e));
        _loop_m = crane_raw(a0);
      }
    }
  }

  template <typename T1, typename F0, typename F3>
  static bool equal_more(F0 &&cmp, typename X::t x1, const T1 &d1, F3 &&cont,
                         const enumeration<T1> &e2) {
    if (std::holds_alternative<typename enumeration<T1>::End>(e2.v())) {
      return false;
    } else {
      const auto &[a0, a1, a2, a3] =
          std::get<typename enumeration<T1>::More>(e2.v());
      auto &&_sv = X::compare(std::move(x1), a0);
      if (std::holds_alternative<typename Compare<typename X::t>::EQ>(_sv.v())) {
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
  static bool
  equal_cont(F0 &&cmp, const tree<T1> &m1,
             const std::type_identity_t<crane::fn<bool(enumeration<T1>)>> &cont,
             const enumeration<T1> &e2) {
    // Loop replaces the tail recursion: each recursive call updates the loop
    // variables.
    std::type_identity_t<crane::fn<bool(enumeration<T1>)>> _loop_cont = cont;
    const tree<T1> *_loop_m1 = &m1;
    while (true) {
      if (std::holds_alternative<typename tree<T1>::Leaf>(_loop_m1->v())) {
        return _loop_cont(e2);
      } else {
        const auto &[a0, a1, a2, a3, _] =
            std::get<typename tree<T1>::Node>(_loop_m1->v());
        const tree<T1> &a0_value = *a0;
        const tree<T1> &a3_value = *a3;
        _loop_cont =
            [=, a1 = a1, a2 = a2, a3_value = a3_value](enumeration<T1> _x0) -> bool {
              return equal_more<T1>(
                  cmp, a1, a2, [=, _loop_cont = _loop_cont, a3_value = a3_value,
                                cmp = cmp](enumeration<T1> _x0) -> bool {
                                 return equal_cont<T1>(cmp, a3_value,
                                                       _loop_cont, _x0);
                               },
                  _x0);
            };
        _loop_m1 = &a0_value;
      }
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
  static bool equal(F0 &&cmp, const tree<T1> &m1, const tree<T1> &m2) {
    return equal_cont<T1>(cmp, m1, equal_end<T1>,
                          cons<T1>(m2, enumeration<T1>::end()));
  }

  template <typename T1, typename T2, typename F0>
    requires std::is_invocable_r_v<T2, F0 &, T1 &>
  static tree<T2> map(F0 &&f, const tree<T1> &m) {
    // Explicit stack replaces the non-tail recursion of map: _call frames are
    // pending calls, _after frames resume a caller.
    struct _call {
      const tree<T1> *m;
    };

    struct _after_map_in_Node {
      typename X::t a1;
      T1 a2;
      const tree<T1> *a3;
      typename I::t a4;
    };

    struct _after_map_in_Node_2 {
      typename X::t a1;
      T1 a2;
      typename I::t a4;
      tree<T2> _tmp2;
    };

    using _frame =
        std::variant<_call, _after_map_in_Node, _after_map_in_Node_2>;
    tree<T2> _result{};
    crane::small_vector<_frame> _stack;
    _stack.emplace_back(_call{&m});
    while (!_stack.empty()) {
      _frame &_popped = _stack.back();
      if (std::holds_alternative<_call>(_popped)) {
        auto _f = std::move(std::get<_call>(_popped));
        _stack.pop_back();
        const tree<T1> &m = *_f.m;
        if (std::holds_alternative<typename tree<T1>::Leaf>(m.v())) {
          _result = tree<T2>::leaf();
        } else {
          const auto &[a0, a1, a2, a3, a4] =
              std::get<typename tree<T1>::Node>(m.v());
          _stack.emplace_back(_after_map_in_Node{a1, a2, crane_raw(a3), a4});
          _stack.emplace_back(_call{crane_raw(a0)});
        }
      } else if (std::holds_alternative<_after_map_in_Node>(_popped)) {
        auto _f = std::move(std::get<_after_map_in_Node>(_popped));
        _stack.pop_back();
        typename X::t a1 = std::move(_f.a1);
        auto a2 = std::move(_f.a2);
        const tree<T1> &a3 = *_f.a3;
        typename I::t a4 = std::move(_f.a4);
        _stack.emplace_back(_after_map_in_Node_2{
            std::move(a1), std::move(a2), std::move(a4), std::move(_result)});
        _stack.emplace_back(_call{&a3});
      } else {
        auto _f = std::move(std::get<_after_map_in_Node_2>(_popped));
        _stack.pop_back();
        typename X::t a1 = std::move(_f.a1);
        auto a2 = std::move(_f.a2);
        typename I::t a4 = std::move(_f.a4);
        _result = tree<T2>::node(std::move(_f._tmp2), std::move(a1), f(a2),
                                 std::move(_result), std::move(a4));
      }
    }
    return _result;
  }

  template <typename T1, typename T2, typename F0>
    requires std::is_invocable_r_v<T2, F0 &, typename X::t &, T1 &>
  static tree<T2> mapi(F0 &&f, const tree<T1> &m) {
    // Explicit stack replaces the non-tail recursion of mapi: _call frames are
    // pending calls, _after frames resume a caller.
    struct _call {
      const tree<T1> *m;
    };

    struct _after_mapi_in_Node {
      typename X::t a1;
      T1 a2;
      const tree<T1> *a3;
      typename I::t a4;
    };

    struct _after_mapi_in_Node_2 {
      typename X::t a1;
      T1 a2;
      typename I::t a4;
      tree<T2> _tmp2;
    };

    using _frame =
        std::variant<_call, _after_mapi_in_Node, _after_mapi_in_Node_2>;
    tree<T2> _result{};
    crane::small_vector<_frame> _stack;
    _stack.emplace_back(_call{&m});
    while (!_stack.empty()) {
      _frame &_popped = _stack.back();
      if (std::holds_alternative<_call>(_popped)) {
        auto _f = std::move(std::get<_call>(_popped));
        _stack.pop_back();
        const tree<T1> &m = *_f.m;
        if (std::holds_alternative<typename tree<T1>::Leaf>(m.v())) {
          _result = tree<T2>::leaf();
        } else {
          const auto &[a0, a1, a2, a3, a4] =
              std::get<typename tree<T1>::Node>(m.v());
          _stack.emplace_back(_after_mapi_in_Node{a1, a2, crane_raw(a3), a4});
          _stack.emplace_back(_call{crane_raw(a0)});
        }
      } else if (std::holds_alternative<_after_mapi_in_Node>(_popped)) {
        auto _f = std::move(std::get<_after_mapi_in_Node>(_popped));
        _stack.pop_back();
        typename X::t a1 = std::move(_f.a1);
        auto a2 = std::move(_f.a2);
        const tree<T1> &a3 = *_f.a3;
        typename I::t a4 = std::move(_f.a4);
        _stack.emplace_back(_after_mapi_in_Node_2{
            std::move(a1), std::move(a2), std::move(a4), std::move(_result)});
        _stack.emplace_back(_call{&a3});
      } else {
        auto _f = std::move(std::get<_after_mapi_in_Node_2>(_popped));
        _stack.pop_back();
        typename X::t a1 = std::move(_f.a1);
        auto a2 = std::move(_f.a2);
        typename I::t a4 = std::move(_f.a4);
        _result = tree<T2>::node(std::move(_f._tmp2), a1, f(a1, a2),
                                 std::move(_result), std::move(a4));
      }
    }
    return _result;
  }

  template <typename T1, typename T2, typename F0>
    requires std::is_invocable_r_v<std::optional<T2>, F0 &,
                                   const typename X::t &, const T1 &>
  static tree<T2> map_option(F0 &&f, const tree<T1> &m) {
    // Explicit stack replaces the non-tail recursion of map_option: _call
    // frames are pending calls, _after frames resume a caller.
    struct _call {
      const tree<T1> *m;
    };

    struct _after_map_option_in_None {
      const tree<T1> *a3;
    };

    struct _after_map_option_in_None_2 {
      tree<T2> _tmp4;
    };

    struct _after_map_option_in_Some {
      typename X::t a1;
      const tree<T1> *a3;
      T2 d_;
    };

    struct _after_map_option_in_Some_2 {
      typename X::t a1;
      T2 d_;
      tree<T2> _tmp2;
    };

    using _frame = std::variant<
        _call, _after_map_option_in_None, _after_map_option_in_None_2,
        _after_map_option_in_Some, _after_map_option_in_Some_2>;
    tree<T2> _result{};
    crane::small_vector<_frame> _stack;
    _stack.emplace_back(_call{&m});
    while (!_stack.empty()) {
      _frame &_popped = _stack.back();
      if (std::holds_alternative<_call>(_popped)) {
        auto _f = std::move(std::get<_call>(_popped));
        _stack.pop_back();
        const tree<T1> &m = *_f.m;
        if (std::holds_alternative<typename tree<T1>::Leaf>(m.v())) {
          _result = tree<T2>::leaf();
        } else {
          const auto &[a0, a1, a2, a3, _] =
              std::get<typename tree<T1>::Node>(m.v());
          auto _cs = f(a1, a2);
          if (_cs.has_value()) {
            const T2 &d_ = *_cs;
            _stack.emplace_back(
                _after_map_option_in_Some{a1, crane_raw(a3), d_});
            _stack.emplace_back(_call{crane_raw(a0)});
          } else {
            _stack.emplace_back(_after_map_option_in_None{crane_raw(a3)});
            _stack.emplace_back(_call{crane_raw(a0)});
          }
        }
      } else if (std::holds_alternative<_after_map_option_in_None>(_popped)) {
        auto _f = std::move(std::get<_after_map_option_in_None>(_popped));
        _stack.pop_back();
        const tree<T1> &a3 = *_f.a3;
        _stack.emplace_back(_after_map_option_in_None_2{std::move(_result)});
        _stack.emplace_back(_call{&a3});
      } else if (std::holds_alternative<_after_map_option_in_None_2>(_popped)) {
        auto _f = std::move(std::get<_after_map_option_in_None_2>(_popped));
        _stack.pop_back();
        _result = concat<T2>(std::move(_f._tmp4), std::move(_result));
      } else if (std::holds_alternative<_after_map_option_in_Some>(_popped)) {
        auto _f = std::move(std::get<_after_map_option_in_Some>(_popped));
        _stack.pop_back();
        typename X::t a1 = std::move(_f.a1);
        const tree<T1> &a3 = *_f.a3;
        auto d_ = std::move(_f.d_);
        _stack.emplace_back(_after_map_option_in_Some_2{
            std::move(a1), std::move(d_), std::move(_result)});
        _stack.emplace_back(_call{&a3});
      } else {
        auto _f = std::move(std::get<_after_map_option_in_Some_2>(_popped));
        _stack.pop_back();
        typename X::t a1 = std::move(_f.a1);
        auto d_ = std::move(_f.d_);
        _result = join<T2>(std::move(_f._tmp2), std::move(a1), std::move(d_),
                           std::move(_result));
      }
    }
    return _result;
  }

  template <typename T1, typename T2, typename T3, typename F0, typename F1,
            typename F2>
    requires std::is_invocable_r_v<std::optional<T3>, F0 &,
                                   const typename X::t &, const T1 &,
                                   std::optional<T2> &&> &&
             std::is_invocable_r_v<tree<T3>, F1 &, const tree<T1> &> &&
             std::is_invocable_r_v<tree<T3>, F2 &, tree<T2> &&>
  static tree<T3> map2_opt(F0 &&f, F1 &&mapl, F2 &&mapr, const tree<T1> &m1,
                           const tree<T2> &m2) {
    // Explicit stack replaces the non-tail recursion of map2_opt: _call frames
    // are pending calls, _after frames resume a caller.
    struct _call {
      tree<T2> m2;
      const tree<T1> *m1;
    };

    struct _after_map2_opt_in_None {
      const tree<T1> *a3;
      tree<T2> r2_;
    };

    struct _after_map2_opt_in_None_2 {
      tree<T3> _tmp4;
    };

    struct _after_map2_opt_in_Some {
      typename X::t a1;
      const tree<T1> *a3;
      tree<T2> r2_;
      T3 e;
    };

    struct _after_map2_opt_in_Some_2 {
      typename X::t a1;
      T3 e;
      tree<T3> _tmp2;
    };

    using _frame =
        std::variant<_call, _after_map2_opt_in_None, _after_map2_opt_in_None_2,
                     _after_map2_opt_in_Some, _after_map2_opt_in_Some_2>;
    tree<T3> _result{};
    crane::small_vector<_frame> _stack;
    _stack.emplace_back(_call{m2, &m1});
    while (!_stack.empty()) {
      _frame &_popped = _stack.back();
      if (std::holds_alternative<_call>(_popped)) {
        auto _f = std::move(std::get<_call>(_popped));
        _stack.pop_back();
        tree<T2> m2 = std::move(_f.m2);
        const tree<T1> &m1 = *_f.m1;
        if (std::holds_alternative<typename tree<T1>::Leaf>(m1.v())) {
          _result = mapr(std::move(m2));
        } else {
          const auto &[a0, a1, a2, a3, _] =
              std::get<typename tree<T1>::Node>(m1.v());
          if (std::holds_alternative<typename tree<T2>::Leaf>(m2.v())) {
            _result = mapl(m1);
          } else {
            auto _cs = split<T2>(a1, m2);
            tree<T2> l2_ = std::move(_cs).t_left;
            std::optional<T2> o2 = std::move(_cs).t_opt;
            tree<T2> r2_ = std::move(_cs).t_right;
            auto _cs1 = f(a1, a2, std::move(o2));
            if (_cs1.has_value()) {
              const T3 &e = *_cs1;
              _stack.emplace_back(
                  _after_map2_opt_in_Some{a1, crane_raw(a3), std::move(r2_),
                                          e});
              _stack.emplace_back(_call{std::move(l2_), crane_raw(a0)});
            } else {
              _stack.emplace_back(
                  _after_map2_opt_in_None{crane_raw(a3), std::move(r2_)});
              _stack.emplace_back(_call{std::move(l2_), crane_raw(a0)});
            }
          }
        }
      } else if (std::holds_alternative<_after_map2_opt_in_None>(_popped)) {
        auto _f = std::move(std::get<_after_map2_opt_in_None>(_popped));
        _stack.pop_back();
        const tree<T1> &a3 = *_f.a3;
        tree<T2> r2_ = std::move(_f.r2_);
        _stack.emplace_back(_after_map2_opt_in_None_2{std::move(_result)});
        _stack.emplace_back(_call{std::move(r2_), &a3});
      } else if (std::holds_alternative<_after_map2_opt_in_None_2>(_popped)) {
        auto _f = std::move(std::get<_after_map2_opt_in_None_2>(_popped));
        _stack.pop_back();
        _result = concat<T3>(std::move(_f._tmp4), std::move(_result));
      } else if (std::holds_alternative<_after_map2_opt_in_Some>(_popped)) {
        auto _f = std::move(std::get<_after_map2_opt_in_Some>(_popped));
        _stack.pop_back();
        typename X::t a1 = std::move(_f.a1);
        const tree<T1> &a3 = *_f.a3;
        tree<T2> r2_ = std::move(_f.r2_);
        auto e = std::move(_f.e);
        _stack.emplace_back(_after_map2_opt_in_Some_2{
            std::move(a1), std::move(e), std::move(_result)});
        _stack.emplace_back(_call{std::move(r2_), &a3});
      } else {
        auto _f = std::move(std::get<_after_map2_opt_in_Some_2>(_popped));
        _stack.pop_back();
        typename X::t a1 = std::move(_f.a1);
        auto e = std::move(_f.e);
        _result = join<T3>(std::move(_f._tmp2), std::move(a1), std::move(e),
                           std::move(_result));
      }
    }
    return _result;
  }

  template <typename T1, typename T2, typename T3>
  static tree<T3> map2(std::type_identity_t<
      crane::fn<std::optional<T3>(std::optional<T1>, std::optional<T2>)>> f,
                       const tree<T1> &x0_, const tree<T2> &x1_) {
    return map2_opt<T1, T2, T3>(
        [=](key, const T1 &d,
            const std::optional<T2> &o) {
          return f(std::make_optional<T1>(d), o);
        },
        [=](tree<T1> _x0) -> tree<T3> {
          return map_option<T1, T3>([=, f = f](key,
                                               const T1 &d) {
            return f(std::make_optional<T1>(d), std::optional<T2>());
          },
                                    _x0);
        },
        [=](tree<T2> _x0) -> tree<T3> {
          return map_option<T2, T3>([=, f = f](key,
                                               const T2 &d_) {
            return f(std::optional<T1>(), std::make_optional<T2>(d_));
          },
                                    _x0);
        },
        x0_,
        x1_);
  }

  struct Proofs {
    using MX = OrderedTypeFacts<X>;
    using PX = KeyOrderedType<X>;
    using L = Coq_Raw<X>;

    template <typename T1, typename T2, typename F0>
    static T2 fold_(F0 &&f, const tree<T1> &s, const T2 &x0_) {
      return L::template fold<T1, T2>(f, elements<T1>(s), x0_);
    }

    template <typename T1>
    static List<std::pair<key, T1>> flatten_e(const enumeration<T1> &e) {
      // Explicit stack replaces the non-tail recursion of flatten_e: _call
      // frames are pending calls, _after frames resume a caller.
      struct _call {
        const enumeration<T1> *e;
      };

      struct _after_flatten_e_in_More {
        typename X::t a0;
        T1 a1;
        tree<T1> a2;
      };

      using _frame = std::variant<_call, _after_flatten_e_in_More>;
      List<std::pair<key, T1>> _result{};
      crane::small_vector<_frame> _stack;
      _stack.emplace_back(_call{&e});
      while (!_stack.empty()) {
        _frame &_popped = _stack.back();
        if (std::holds_alternative<_call>(_popped)) {
          auto _f = std::move(std::get<_call>(_popped));
          _stack.pop_back();
          const enumeration<T1> &e = *_f.e;
          if (std::holds_alternative<typename enumeration<T1>::End>(e.v())) {
            _result = List<std::pair<typename X::t, T1>>::nil();
          } else {
            const auto &[a0, a1, a2, a3] =
                std::get<typename enumeration<T1>::More>(e.v());
            _stack.emplace_back(_after_flatten_e_in_More{a0, a1, a2});
            _stack.emplace_back(_call{crane_raw(a3)});
          }
        } else {
          auto _f = std::move(std::get<_after_flatten_e_in_More>(_popped));
          _stack.pop_back();
          typename X::t a0 = std::move(_f.a0);
          auto a1 = std::move(_f.a1);
          tree<T1> a2 = std::move(_f.a2);
          _result = List<std::pair<typename X::t, T1>>::cons(
              std::make_pair(std::move(a0), std::move(a1)),
              elements<T1>(std::move(a2)).app(std::move(_result)));
        }
      }
      return _result;
    }
  };
};

template <Int I, OrderedType X> struct IntMake {
  using E = X;
  using Raw = Raw<I, X>;

  template <typename elt> struct bst {
    typename Raw::template tree<elt> this_;

    // ACCESSORS
    template <typename CraneU> operator bst<CraneU>() const {
      return {crane_convert<typename Raw::template tree<CraneU>>(this_)};
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
  static t<T2> map(F0 &&f, const bst<T1> &m) {
    return bst<T2>{Raw::template map<T1, T2>(f, m.this_)};
  }

  template <typename T1, typename T2, typename F0>
  static t<T2> mapi(F0 &&f, const bst<T1> &m) {
    return bst<T2>{Raw::template mapi<T1, T2>(f, m.this_)};
  }

  template <typename T1, typename T2, typename T3, typename F0>
  static t<T3> map2(F0 &&f, const bst<T1> &m, const bst<T2> &m_) {
    return bst<T3>{Raw::template map2<T1, T2, T3>(f, m.this_, m_.this_)};
  }

  template <typename T1>
  static List<std::pair<key, T1>> elements(const bst<T1> &m) {
    return Raw::template elements<T1>(m.this_);
  }

  template <typename T1> static uint64_t cardinal(const bst<T1> &m) {
    return Raw::template cardinal<T1>(m.this_);
  }

  template <typename T1, typename T2, typename F0>
  static T2 fold(F0 &&f, const bst<T1> &m, const T2 &i) {
    return Raw::template fold<T1, T2>(f, m.this_, i);
  }

  template <typename T1, typename F0>
  static bool equal(F0 &&cmp, const bst<T1> &m, const bst<T1> &m_) {
    return Raw::template equal<T1>(cmp, m.this_, m_.this_);
  }
};

template <OrderedType X> struct Make : IntMake<Z_as_Int, X> {};

using node = std::pair<uint64_t, uint64_t>;

struct Op {
  // TYPES
  struct Union {
    uint64_t x;
    uint64_t y;
  };

  struct Same {
    uint64_t x;
    uint64_t y;
  };

  using variant_t = std::variant<Union, Same>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Op() {}

  explicit Op(Union _v) : v_(std::move(_v)) {}

  explicit Op(Same _v) : v_(std::move(_v)) {}

  static Op Union_(uint64_t x, uint64_t y) { return Op(Union{x, y}); }

  static Op same(uint64_t x, uint64_t y) { return Op(Same{x, y}); }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

void init_ST(STRefs r, std::span<std::pair<uint64_t, uint64_t>> a, uint64_t n,
             uint64_t i);
std::shared_ptr<crane::array_storage<node>> make_ST(STRefs r, uint64_t n);
uint64_t find_ST(STRefs r, std::span<std::pair<uint64_t, uint64_t>> a,
                 uint64_t fuel, uint64_t x);
void union_ST(STRefs r, uint64_t n, std::span<std::pair<uint64_t, uint64_t>> a,
              uint64_t x, uint64_t y);
bool same_ST(STRefs r, uint64_t n, std::span<std::pair<uint64_t, uint64_t>> a,
             uint64_t x, uint64_t y);
List<bool> run_ST(STRefs r, uint64_t n,
                  std::span<std::pair<uint64_t, uint64_t>> a,
                  const List<Op> &ops);
List<bool> union_find_ST(STRefs r, uint64_t n, const List<Op> &ops);
using NatMap = Make<Nat_as_OT>;
using uf = NatMap::template t<node>;
[[gnu::used]] inline const uf empty_uf = NatMap::template empty<node>();
node get(const NatMap::template bst<std::pair<uint64_t, uint64_t>> &s,
         uint64_t x);
std::pair<uint64_t, uf>
find_fun(uint64_t fuel,
         const NatMap::template bst<std::pair<uint64_t, uint64_t>> &s,
         uint64_t x);
uf union_fun(uint64_t n,
             const NatMap::template bst<std::pair<uint64_t, uint64_t>> &s,
             uint64_t x, uint64_t y);
std::pair<bool, uf>
same_fun(uint64_t n,
         const NatMap::template bst<std::pair<uint64_t, uint64_t>> &s,
         uint64_t x, uint64_t y);
List<bool> run_fun(uint64_t n,
                   const NatMap::template bst<std::pair<uint64_t, uint64_t>> &s,
                   const List<Op> &ops);

struct UnionFind {
  static List<bool> union_find_ST(uint64_t x0_, const List<Op> &x1_);
  static List<bool> union_find_fun(uint64_t n, const List<Op> &ops);
};
