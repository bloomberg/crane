#ifndef INCLUDED_ETA_EXPANDED_CLASS_METHOD_PARAM_ERASED
#define INCLUDED_ETA_EXPANDED_CLASS_METHOD_PARAM_ERASED

#include "crane_fn.h"
#include "obj.h"
#include "small_vector.h"
#include <any>
#include <atomic>
#include <concepts>
#include <memory>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

struct map_alist;
struct Nat;
template <typename A> struct List;
template <typename I, typename K, typename V, typename M>
concept Map = requires {
  { I::empty() } -> std::convertible_to<M>;
  {
    I::add(std::declval<K>(), std::declval<V>(), std::declval<M>())
  } -> std::convertible_to<M>;
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
  Nat(Nat &&) noexcept = default;
  Nat &operator=(Nat &&) noexcept = default;

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
    requires std::is_invocable_r_v<T1, F0 &, A &, T1 &>
  T1 fold_right(F0 &&f, T1 a0) const {
    const List<A> *_self = this;

    /// _Enter: captures varying parameters for each recursive call.
    struct _Enter {
      const List<A> *_self;
    };

    /// _Cont_Cons: saves [a1], resumes after recursive call, then processes
    /// rest.
    struct _Cont_Cons {
      A a1;
    };

    using _Frame = std::variant<_Enter, _Cont_Cons>;
    T1 _result{};
    crane::small_vector<_Frame> _stack;
    _stack.emplace_back(_Enter{_self});
    /// Loopified fold_right: _Enter -> _Cont_Cons.
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
          _stack.emplace_back(_Cont_Cons{a1});
          _stack.emplace_back(_Enter{crane_raw(a2)});
        }
      } else {
        auto _f = std::move(std::get<_Cont_Cons>(_frame));
        auto a1 = std::move(_f.a1);
        T1 r_ = std::move(_result);
        _result = f(a1, std::move(r_));
      }
    }
    return _result;
  }
};

struct map_alist {
  static List<std::pair<Nat, Nat>> empty() {
    return List<std::pair<Nat, Nat>>::nil();
  }

  static List<std::pair<Nat, Nat>> add(Nat k, Nat v,
                                       List<std::pair<Nat, Nat>> m) {
    return List<std::pair<Nat, Nat>>::cons(std::make_pair(k, v), std::move(m));
  }
};

static_assert(Map<map_alist, Nat, Nat, List<std::pair<Nat, Nat>>>);
List<std::pair<Nat, Nat>> build(const List<std::pair<Nat, Nat>> &l);
List<std::pair<Nat, Nat>> build_saturated(const List<std::pair<Nat, Nat>> &l);

template <typename F0>
  requires std::is_invocable_r_v<List<std::pair<Nat, Nat>>, F0 &,
                                 List<std::pair<Nat, Nat>> &>
List<std::pair<Nat, Nat>> apply_it(F0 &&f, List<std::pair<Nat, Nat>> x0_) {
  return f(std::move(x0_));
}

List<std::pair<Nat, Nat>> partial(const Nat &k, const Nat &v,
                                  const List<std::pair<Nat, Nat>> &l);

#endif // INCLUDED_ETA_EXPANDED_CLASS_METHOD_PARAM_ERASED
