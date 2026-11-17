#ifndef INCLUDED_HKT_CLASS_PARAM
#define INCLUDED_HKT_CLASS_PARAM

#include "crane_fn.h"
#include "obj.h"
#include "small_vector.h"
#include <atomic>
#include <concepts>
#include <cstdint>
#include <memory>
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

  uint64_t length() const {
    const List<A> *_self = this;

    // Explicit stack replaces the non-tail recursion of length: _call frames
    // are pending calls, _after frames resume a caller.
    struct _call {
      const List<A> *_self;
    };

    struct _after_length_in_Cons {};

    using _frame = std::variant<_call, _after_length_in_Cons>;
    uint64_t _result{};
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
          _result = UINT64_C(0);
        } else {
          const auto &[_, a1] = std::get<typename List<A>::Cons>(_sv.v());
          _stack.emplace_back(_after_length_in_Cons{});
          _stack.emplace_back(_call{crane_raw(a1)});
        }
      } else {
        auto _f = std::move(std::get<_after_length_in_Cons>(_popped));
        _stack.pop_back();
        _result = (std::move(_result) + 1);
      }
    }
    return _result;
  }
};

/// A type class parameterised over a type {i constructor} (C : Type -> Type).
/// Crane emits the instance's methods against the shared List type but
/// erases the element type, producing List<std::any> parameters where
/// List<Nat> is required, which corrupts the mapped List type itself.
template <typename I>
concept Container = requires {
  typename I::template C<crane::obj>;
  {
    I::template empty<crane::obj>()
  } -> std::convertible_to<typename I::template C<crane::obj>>;
  {
    I::template insert<crane::obj>(
        std::declval<crane::obj>(),
        std::declval<typename I::template C<crane::obj>>())
  } -> std::convertible_to<typename I::template C<crane::obj>>;
  {
    I::template toList<crane::obj>(
        std::declval<typename I::template C<crane::obj>>())
  } -> std::convertible_to<List<crane::obj>>;
};

struct HktClassParam {
  template <Container _tcI0, typename T2>
  static typename _tcI0::template C<T2> empty() {
    return _tcI0::template empty<T2>();
  }

  template <Container _tcI0, typename T2>
  static typename _tcI0::template C<T2>
  insert(const T2 &x, typename _tcI0::template C<T2> x0) {
    return _tcI0::template insert<T2>(x, std::move(x0));
  }

  template <Container _tcI0, typename T2>
  static List<T2> toList(typename _tcI0::template C<T2> x) {
    return _tcI0::template toList<T2>(std::move(x));
  }

  struct ListContainer {
    template <typename CraneA0> using C = List<CraneA0>;

    template <typename CraneA0> static List<CraneA0> empty() {
      return List<CraneA0>::nil();
    }

    template <typename CraneA0>
    static List<CraneA0> insert(CraneA0 x, List<CraneA0> xs) {
      return List<CraneA0>::cons(std::move(x), std::move(xs));
    }

    template <typename CraneA0> static List<CraneA0> toList(List<CraneA0> xs) {
      return xs;
    }
  };

  static_assert(Container<ListContainer>);

  template <Container _tcI0>
  static typename _tcI0::template C<uint64_t> build(const List<uint64_t> &l) {
    return l.template fold_right<typename _tcI0::template C<uint64_t>>(
        [](uint64_t n,
           typename _tcI0::template C<uint64_t> acc) {
          return _tcI0::template insert<uint64_t>(n, std::move(acc));
        },
        _tcI0::template empty<uint64_t>());
  }

  static uint64_t run(uint64_t k);
};

#endif // INCLUDED_HKT_CLASS_PARAM
