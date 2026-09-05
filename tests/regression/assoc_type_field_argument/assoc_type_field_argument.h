#ifndef INCLUDED_ASSOC_TYPE_FIELD_ARGUMENT
#define INCLUDED_ASSOC_TYPE_FIELD_ARGUMENT

#include "crane_fn.h"
#include "small_vector.h"
#include <any>
#include <atomic>
#include <concepts>
#include <memory>
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
  template <typename c> using elt = std::any;

  struct CNat {
    using elt = uint64_t;

    static List<uint64_t> empty() { return List<uint64_t>::nil(); }

    static List<uint64_t> insert(uint64_t x, List<uint64_t> c) {
      return List<uint64_t>::cons(x, c);
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
      return List<std::pair<uint64_t, uint64_t>>::cons(x, c);
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

  static inline const uint64_t total =
      (CNat::size(build3<CNat, List<uint64_t>>(UINT64_C(1), UINT64_C(2),
                                               UINT64_C(3))) +
       CPair::size(build3<CPair, List<std::pair<uint64_t, uint64_t>>>(
           std::make_pair(UINT64_C(1), UINT64_C(1)),
           std::make_pair(UINT64_C(2), UINT64_C(2)),
           std::make_pair(UINT64_C(3), UINT64_C(3)))));
};

#endif // INCLUDED_ASSOC_TYPE_FIELD_ARGUMENT
