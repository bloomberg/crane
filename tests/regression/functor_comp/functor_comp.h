#ifndef INCLUDED_FUNCTOR_COMP
#define INCLUDED_FUNCTOR_COMP

#include "crane_fn.h"
#include "obj.h"
#include "small_vector.h"
#include <atomic>
#include <concepts>
#include <cstdint>
#include <memory>
#include <optional>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

template <typename A> struct List;

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
    requires std::is_invocable_r_v<T1, F0 &, T1 &&, const A &>
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

    /// CraneEnter: captures varying parameters for each recursive call.
    struct CraneEnter {
      const List<A> *_self;
    };

    /// CraneCont_Cons: saves [a0], resumes after recursive call, then processes
    /// rest.
    struct CraneCont_Cons {
      A a0;
    };

    using CraneFrame = std::variant<CraneEnter, CraneCont_Cons>;
    List<A> _result{};
    crane::small_vector<CraneFrame> _stack;
    _stack.emplace_back(CraneEnter{_self});
    /// Loopified rev: CraneEnter -> CraneCont_Cons.
    while (!_stack.empty()) {
      CraneFrame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<CraneEnter>(_frame)) {
        auto _f = std::move(std::get<CraneEnter>(_frame));
        const List<A> *_self = _f._self;
        auto &&_sv = *_self;
        if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
          _result = List<A>::nil();
        } else {
          const auto &[a0, a1] = std::get<typename List<A>::Cons>(_sv.v());
          _stack.emplace_back(CraneCont_Cons{a0});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        }
      } else {
        auto _f = std::move(std::get<CraneCont_Cons>(_frame));
        auto a0 = std::move(_f.a0);
        _result = std::move(_result).app(List<A>::cons(a0, List<A>::nil()));
      }
    }
    return _result;
  }

  uint64_t length() const {
    const List<A> *_self = this;

    /// CraneEnter: captures varying parameters for each recursive call.
    struct CraneEnter {
      const List<A> *_self;
    };

    /// CraneCont_Cons: resumes after recursive call, then processes rest.
    struct CraneCont_Cons {};

    using CraneFrame = std::variant<CraneEnter, CraneCont_Cons>;
    uint64_t _result{};
    crane::small_vector<CraneFrame> _stack;
    _stack.emplace_back(CraneEnter{_self});
    /// Loopified length: CraneEnter -> CraneCont_Cons.
    while (!_stack.empty()) {
      CraneFrame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<CraneEnter>(_frame)) {
        auto _f = std::move(std::get<CraneEnter>(_frame));
        const List<A> *_self = _f._self;
        auto &&_sv = *_self;
        if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
          _result = UINT64_C(0);
        } else {
          const auto &[a0, a1] = std::get<typename List<A>::Cons>(_sv.v());
          _stack.emplace_back(CraneCont_Cons{});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        }
      } else {
        auto _f = std::move(std::get<CraneCont_Cons>(_frame));
        _result = (std::move(_result) + 1);
      }
    }
    return _result;
  }

  List<A> app(List<A> m) const {
    std::optional<List<A>> _root{};
    std::shared_ptr<List<A>> *_write = nullptr;
    const List<A> *_loop_self = this;
    List<A> _loop_m = std::move(m);
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
        auto _value = std::move(_loop_m);
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
    static t push(uint64_t x, const List<uint64_t> &s);
    static std::optional<std::pair<uint64_t, t>> pop(const List<uint64_t> &s);
    static uint64_t size(t x0_);
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
          [](typename C::t acc, uint64_t x) { return C::push(x, acc); },
          std::move(c));
    }

    static List<uint64_t> to_list(typename C::t c) {
      {
        uint64_t _lc1_fuel = C::size(c);
        const List<uint64_t> &_lc1_acc = List<uint64_t>::nil();
        typename C::t _lc1_c0 = std::move(c);
        typename C::t _lc1_loop_c0 = std::move(_lc1_c0);
        List<uint64_t> _lc1_loop_acc = _lc1_acc;
        uint64_t _lc1_loop_fuel = std::move(_lc1_fuel);
        while (true) {
          if (_lc1_loop_fuel <= 0) {
            return _lc1_loop_acc.rev();
          } else {
            uint64_t f = _lc1_loop_fuel - 1;
            auto _cs = C::pop(_lc1_loop_c0);
            if (_cs.has_value()) {
              const std::pair<uint64_t, typename C::t> &p = *_cs;
              const auto &[x, c_] = p;
              _lc1_loop_c0 = c_;
              _lc1_loop_acc = List<uint64_t>::cons(x, _lc1_loop_acc);
              _lc1_loop_fuel = f;
            } else {
              return _lc1_loop_acc.rev();
            }
          }
        }
      }
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
