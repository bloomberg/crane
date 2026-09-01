#ifndef INCLUDED_FUNCTOR_COMP
#define INCLUDED_FUNCTOR_COMP

#include "crane_fn.h"
#include "small_vector.h"
#include <any>
#include <atomic>
#include <concepts>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

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
      this->v_ = Cons{
          [&]() -> A {
            if constexpr (std::is_same_v<_U, std::any>) {
              if (a.type() == typeid(A))
                return std::any_cast<A>(a);
              if constexpr (requires {
                              typename A::first_type;
                              typename A::second_type;
                            }) {
                const auto &[_k, _v] =
                    std::any_cast<std::pair<std::any, std::any>>(a);
                return A{[&]() -> typename A::first_type {
                           if constexpr (std::is_same_v<typename A::first_type,
                                                        std::any>)
                             return _k;
                           else
                             return std::any_cast<typename A::first_type>(_k);
                         }(),
                         [&]() -> typename A::second_type {
                           if constexpr (std::is_same_v<typename A::second_type,
                                                        std::any>)
                             return _v;
                           else
                             return std::any_cast<typename A::second_type>(_v);
                         }()};
              }
              return std::any_cast<A>(a);
            } else
              return A(a);
          }(),
          l ? std::make_shared<List<A>>(*l) : nullptr};
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
    requires std::is_invocable_r_v<T1, F0 &, T1 &, A &>
  T1 fold_left(F0 &&f, T1 a0) const {
    const List<A> *_loop_self = this;
    T1 _loop_a0 = std::move(a0);
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
        return _loop_a0;
      } else {
        const auto &[a1, a2] = std::get<typename List<A>::Cons>(_sv.v());
        _loop_self = crane_raw(a2);
        _loop_a0 = f(std::move(_loop_a0), a1);
      }
    }
  }

  List<A> rev() const {
    const List<A> *_self = this;

    /// _Enter: captures varying parameters for each recursive call.
    struct _Enter {
      const List<A> *_self;
    };

    /// _Resume_Cons: saves [_s0], resumes after recursive call with _result.
    struct _Resume_Cons {
      std::decay_t<decltype(List<A>::cons(std::declval<A &>(), List<A>::nil()))>
          _s0;
    };

    using _Frame = std::variant<_Enter, _Resume_Cons>;
    List<A> _result{};
    crane::small_vector<_Frame> _stack;
    _stack.emplace_back(_Enter{_self});
    /// Loopified rev: _Enter -> _Resume_Cons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const List<A> *_self = _f._self;
        auto &&_sv = *_self;
        if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
          _result = List<A>::nil();
        } else {
          const auto &[a0, a1] = std::get<typename List<A>::Cons>(_sv.v());
          _stack.emplace_back(_Resume_Cons{List<A>::cons(a0, List<A>::nil())});
          _stack.emplace_back(_Enter{crane_raw(a1)});
        }
      } else {
        auto _f = std::move(std::get<_Resume_Cons>(_frame));
        _result = std::move(_result).app(_f._s0);
      }
    }
    return _result;
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

template <typename M>
concept CONTAINER = requires {
  typename M::t;
  requires(
      requires {
        { M::empty } -> std::convertible_to<typename M::t>;
      } ||
      requires {
        { M::empty() } -> std::convertible_to<typename M::t>;
      });
  {
    M::push(std::declval<uint64_t>(), std::declval<typename M::t>())
  } -> std::same_as<typename M::t>;
  {
    M::pop(std::declval<typename M::t>())
  } -> std::same_as<std::optional<std::pair<uint64_t, typename M::t>>>;
  { M::size(std::declval<typename M::t>()) } -> std::same_as<uint64_t>;
};

struct FunctorComp {
  struct Stack {
    using t = List<uint64_t>;
    static inline const t empty = List<uint64_t>::nil();
    static t push(uint64_t x, List<uint64_t> s);
    static std::optional<std::pair<uint64_t, t>> pop(const List<uint64_t> &s);
    static uint64_t size(t _x0);
  };

  struct Queue {
    using t = std::pair<List<uint64_t>, List<uint64_t>>;
    static inline const t empty =
        std::make_pair(List<uint64_t>::nil(), List<uint64_t>::nil());
    static t push(uint64_t x, std::pair<List<uint64_t>, List<uint64_t>> q);
    static std::optional<std::pair<uint64_t, t>>
    pop(std::pair<List<uint64_t>, List<uint64_t>> q);
    static uint64_t size(const std::pair<List<uint64_t>, List<uint64_t>> &q);
  };

  template <CONTAINER C> struct ContainerOps {
    static typename C::t push_list(const List<uint64_t> &l, typename C::t c) {
      return l.template fold_left<typename C::t>(
          [](typename C::t acc, uint64_t x) { return C::push(x, acc); }, c);
    }

    static List<uint64_t> to_list(typename C::t c) {
      auto go_impl = [](auto &_self_go, uint64_t fuel, List<uint64_t> acc,
                        typename C::t c0) -> List<uint64_t> {
        if (fuel <= 0) {
          return std::move(acc).rev();
        } else {
          uint64_t f = fuel - 1;
          auto _cs = C::pop(c0);
          if (_cs.has_value()) {
            const std::pair<uint64_t, typename C::t> &p = *_cs;
            const auto &[x, c_] = p;
            return _self_go(_self_go, f,
                            List<uint64_t>::cons(x, std::move(acc)), c_);
          } else {
            return std::move(acc).rev();
          }
        }
      };
      auto go = [&](uint64_t fuel, List<uint64_t> acc,
                    typename C::t c0) -> List<uint64_t> {
        return go_impl(go_impl, fuel, acc, c0);
      };
      return go(C::size(c), List<uint64_t>::nil(), c);
    }
  };

  using StackOps = ContainerOps<Stack>;
  using QueueOps = ContainerOps<Queue>;
  static inline const List<uint64_t> test_stack =
      StackOps::to_list(StackOps::push_list(
          List<uint64_t>::cons(
              UINT64_C(1),
              List<uint64_t>::cons(
                  UINT64_C(2),
                  List<uint64_t>::cons(UINT64_C(3), List<uint64_t>::nil()))),
          Stack::empty));
  static inline const List<uint64_t> test_queue =
      QueueOps::to_list(QueueOps::push_list(
          List<uint64_t>::cons(
              UINT64_C(1),
              List<uint64_t>::cons(
                  UINT64_C(2),
                  List<uint64_t>::cons(UINT64_C(3), List<uint64_t>::nil()))),
          Queue::empty));
  static inline const uint64_t test_stack_size =
      Stack::size(StackOps::push_list(
          List<uint64_t>::cons(
              UINT64_C(10),
              List<uint64_t>::cons(
                  UINT64_C(20),
                  List<uint64_t>::cons(UINT64_C(30), List<uint64_t>::nil()))),
          Stack::empty));
  static inline const uint64_t test_queue_size =
      Queue::size(QueueOps::push_list(
          List<uint64_t>::cons(
              UINT64_C(10),
              List<uint64_t>::cons(
                  UINT64_C(20),
                  List<uint64_t>::cons(UINT64_C(30), List<uint64_t>::nil()))),
          Queue::empty));
};

#endif // INCLUDED_FUNCTOR_COMP
