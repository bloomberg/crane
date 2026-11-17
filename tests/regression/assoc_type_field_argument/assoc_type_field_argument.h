#ifndef INCLUDED_ASSOC_TYPE_FIELD_ARGUMENT
#define INCLUDED_ASSOC_TYPE_FIELD_ARGUMENT

#include "crane_fn.h"
#include "obj.h"
#include "small_vector.h"
#include <atomic>
#include <concepts>
#include <cstdint>
#include <memory>
#include <stdexcept>
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

/// A class's associated Type field used as an argument type: the call
/// site builds the argument at the erased shape (pair<any, any>) while the
/// callee expects the instance's concrete element type.
template <typename I, typename C>
concept Coll = requires {
  typename I::elt;
  { I::empty() } -> std::convertible_to<C>;
  {
    I::insert(std::declval<typename I::elt>(), std::declval<C>())
  } -> std::convertible_to<C>;
  { I::size(std::declval<C>()) } -> std::convertible_to<uint64_t>;
};

struct AssocTypeFieldArgument {
  template <typename c = void> using elt = crane::obj;

  struct CNat {
    using elt = uint64_t;

    static List<uint64_t> empty() { return List<uint64_t>::nil(); }

    static List<uint64_t> insert(uint64_t x, List<uint64_t> c) {
      return List<uint64_t>::cons(x, std::move(c));
    }

    static uint64_t size(List<uint64_t> a0) { return a0.length(); }
  };

  static_assert(Coll<CNat, List<uint64_t>>);

  struct CPair {
    using elt = std::pair<uint64_t, uint64_t>;

    static List<std::pair<uint64_t, uint64_t>> empty() {
      return List<std::pair<uint64_t, uint64_t>>::nil();
    }

    static List<std::pair<uint64_t, uint64_t>>
    insert(std::pair<uint64_t, uint64_t> x,
           List<std::pair<uint64_t, uint64_t>> c) {
      return List<std::pair<uint64_t, uint64_t>>::cons(x, std::move(c));
    }

    static uint64_t size(List<std::pair<uint64_t, uint64_t>> a0) {
      return a0.length();
    }
  };

  static_assert(Coll<CPair, List<std::pair<uint64_t, uint64_t>>>);

  template <typename _tcI0, typename T1>
    requires Coll<_tcI0, T1>
  static T1 build3(const typename _tcI0::elt &a, const typename _tcI0::elt &b,
                   const typename _tcI0::elt &c) {
    return _tcI0::insert(a, _tcI0::insert(b, _tcI0::insert(c, _tcI0::empty())));
  }

  static inline const uint64_t total = (
      CNat::size(
          build3<CNat, List<uint64_t>>(UINT64_C(1), UINT64_C(2), UINT64_C(3))) +
      CPair::size(build3<CPair, List<std::pair<uint64_t, uint64_t>>>(
          std::make_pair(UINT64_C(1), UINT64_C(1)),
          std::make_pair(UINT64_C(2), UINT64_C(2)),
          std::make_pair(UINT64_C(3), UINT64_C(3)))));
};

#endif // INCLUDED_ASSOC_TYPE_FIELD_ARGUMENT
