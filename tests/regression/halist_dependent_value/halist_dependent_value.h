#ifndef INCLUDED_HALIST_DEPENDENT_VALUE
#define INCLUDED_HALIST_DEPENDENT_VALUE

#include "crane_fn.h"
#include "small_vector.h"
#include <any>
#include <atomic>
#include <functional>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

template <typename A> struct List;
template <typename A> struct Sig;
template <typename A, typename P> struct SigT;

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
      this->v_ = Cons{[&]() -> A {
                        if constexpr (std::is_same_v<_U, std::any>) {
                          return crane_any_cast<A>(a);
                        } else {
                          return A(a);
                        }
                      }(),
                      (l ? std::make_shared<List<A>>(*l) : nullptr)};
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

  template <typename F0>
    requires std::is_invocable_r_v<bool, F0 &, A &>
  List<A> filter(F0 &&f) const {
    std::shared_ptr<List<A>> _head{};
    std::shared_ptr<List<A>> *_write = &_head;
    const List<A> *_loop_self = this;
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
        *_write = std::make_shared<List<A>>(List<A>::nil());
        break;
      } else {
        const auto &[a0, a1] = std::get<typename List<A>::Cons>(_sv.v());
        if (f(a0)) {
          auto _cell =
              std::make_shared<List<A>>(typename List<A>::Cons(a0, nullptr));
          *_write = std::move(_cell);
          _write = &std::get<typename List<A>::Cons>((*_write)->v_mut()).l;
          _loop_self = crane_raw(a1);
          continue;
        } else {
          _loop_self = crane_raw(a1);
          continue;
        }
      }
    }
    return std::move(*_head);
  }

  uint64_t length() const {
    const List<A> *_self = this;

    /// _Enter: captures varying parameters for each recursive call.
    struct _Enter {
      const List<A> *_self;
    };

    /// _Resume_Cons: resumes after recursive call with _result.
    struct _Resume_Cons {};

    using _Frame = std::variant<_Enter, _Resume_Cons>;
    uint64_t _result{};
    crane::small_vector<_Frame> _stack;
    _stack.emplace_back(_Enter{_self});
    /// Loopified length: _Enter -> _Resume_Cons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const List<A> *_self = _f._self;
        auto &&_sv = *_self;
        if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
          _result = UINT64_C(0);
        } else {
          const auto &[a0, a1] = std::get<typename List<A>::Cons>(_sv.v());
          _stack.emplace_back(_Resume_Cons{});
          _stack.emplace_back(_Enter{crane_raw(a1)});
        }
      } else {
        auto _f = std::move(std::get<_Resume_Cons>(_frame));
        _result = (std::move(_result) + 1);
      }
    }
    return _result;
  }
};

template <typename A> struct Sig {
  // DATA
  A x;

  // ACCESSORS
  Sig<A> clone() const { return {x}; }

  // CREATORS
  static Sig<A> exist(A x) { return {std::move(x)}; }
};

template <typename A, typename P> struct SigT {
  // DATA
  A x;
  P a1;

  // ACCESSORS
  SigT<A, P> clone() const { return {x, a1}; }

  // CREATORS
  static SigT<A, P> existt(A x, P a1) { return {std::move(x), std::move(a1)}; }

  A projT1() const {
    const auto &[x0, a1] = *this;
    return x0;
  }
};

template <typename a> using EqDec = std::function<bool(a, a)>;

struct Sumbool {
  static Sig<bool> bool_of_sumbool(bool s);
};

template <typename k, typename v> using halist = List<SigT<k, v>>;

struct HAList {
  template <typename T1, typename T2>
  static halist<T1, T2> halist_remove(EqDec<T1> eq, const T1 &k,
                                      const List<SigT<T1, T2>> &m);
  template <typename T1, typename T2>
  static halist<T1, T2> halist_add(EqDec<T1> eq, T1 k, T2 v,
                                   const List<SigT<T1, T2>> &m);
  template <typename T1, typename T2>
  static std::optional<T2> halist_lookup(EqDec<T1> eq, const T1 &k,
                                         const List<SigT<T1, T2>> &l);
};

struct EquivDec {
  template <typename T1>
  static bool equiv_dec(EqDec<T1> eqDec, const T1 &x0_, T1 x1_);
};

/// halist K V is indexed by a value family V : K -> Type.  Crane gives
/// halist_add the signature halist<T1,T2> halist_add(EqDec<T1>, T1 k, T2 v,
/// ...) -- the same template parameter T2 stands for the family and for the
/// value.  T2 is deduced as vty from the map argument, so passing a
/// uint64_t for v leaves no viable overload.
struct HalistDependentValue {
  enum class Key { KNAT, KLIST };

  template <typename T1> static T1 key_rect(T1 f, T1 f0, Key k) {
    switch (k) {
    case Key::KNAT: {
      return f;
    }
    case Key::KLIST: {
      return f0;
    }
    default:
      std::unreachable();
    }
  }

  template <typename T1> static T1 key_rec(T1 f, T1 f0, Key k) {
    switch (k) {
    case Key::KNAT: {
      return f;
    }
    case Key::KLIST: {
      return f0;
    }
    default:
      std::unreachable();
    }
  }

  using vty = std::any;
  static inline const EqDec<Key> keyEq = [](Key x, Key y) {
    switch (x) {
    case Key::KNAT: {
      switch (y) {
      case Key::KNAT: {
        return true;
      }
      case Key::KLIST: {
        return false;
      }
      default:
        std::unreachable();
      }
      break;
    }
    case Key::KLIST: {
      switch (y) {
      case Key::KNAT: {
        return false;
      }
      case Key::KLIST: {
        return true;
      }
      default:
        std::unreachable();
      }
      break;
    }
    default:
      std::unreachable();
    }
  };
  static inline const halist<Key, vty> m0 = List<SigT<Key, std::any>>::nil();
  static inline const halist<Key, vty> m1 =
      HAList::halist_add(keyEq, Key::KNAT, std::any(UINT64_C(7)), m0);
  static inline const halist<Key, vty> m2 = HAList::halist_add(
      keyEq, Key::KLIST,
      std::any(List<std::any>::cons(
          UINT64_C(1),
          List<std::any>::cons(
              UINT64_C(2),
              List<std::any>::cons(UINT64_C(3), List<std::any>::nil())))),
      m1);
  static inline const uint64_t run = ([]() -> uint64_t {
    auto _cs = HAList::halist_lookup(keyEq, Key::KNAT, m2);
    if (_cs.has_value()) {
      const auto &n = *_cs;
      return std::any_cast<uint64_t>(n);
    } else {
      return UINT64_C(0);
    }
  }() + []() -> uint64_t {
    auto _cs1 = HAList::halist_lookup(keyEq, Key::KLIST, m2);
    if (_cs1.has_value()) {
      const auto &l = *_cs1;
      return List<uint64_t>(std::any_cast<List<std::any>>(l)).length();
    } else {
      return UINT64_C(0);
    }
  }());
};

template <typename T1>
bool EquivDec::equiv_dec(EqDec<T1> eqDec, const T1 &x0_, T1 x1_) {
  return eqDec(x0_, x1_);
}

template <typename T1, typename T2>
halist<T1, T2> HAList::halist_remove(EqDec<T1> eq, const T1 &k,
                                     const List<SigT<T1, T2>> &m) {
  return m.filter([=](const SigT<T1, T2> &k_v) mutable {
    return !([=]() mutable {
      const auto &_sv =
          Sumbool::bool_of_sumbool(EquivDec::equiv_dec(eq, k_v.projT1(), k));
      const auto &[x] = _sv;
      return x;
    }());
  });
}

template <typename T1, typename T2>
halist<T1, T2> HAList::halist_add(EqDec<T1> eq, T1 k, T2 v,
                                  const List<SigT<T1, T2>> &m) {
  return List<SigT<T1, T2>>::cons(
      SigT<T1, T2>::existt(k, v),
      HAList::template halist_remove<T1, T2>(eq, k, m));
}

template <typename T1, typename T2>
std::optional<T2> HAList::halist_lookup(EqDec<T1> eq, const T1 &k,
                                        const List<SigT<T1, T2>> &l) {
  if (std::holds_alternative<typename List<SigT<T1, T2>>::Nil>(l.v())) {
    return std::optional<T2>();
  } else {
    const auto &[a0, a1] = std::get<typename List<SigT<T1, T2>>::Cons>(l.v());
    const auto &[x0, a10] = a0;
    if (EquivDec::equiv_dec(eq, x0, k)) {
      return std::make_optional<T2>(a10);
    } else {
      return HAList::template halist_lookup<T1, T2>(eq, k, *a1);
    }
  }
}

#endif // INCLUDED_HALIST_DEPENDENT_VALUE
