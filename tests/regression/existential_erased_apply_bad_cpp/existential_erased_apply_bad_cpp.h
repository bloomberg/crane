#ifndef INCLUDED_EXISTENTIAL_ERASED_APPLY_BAD_CPP
#define INCLUDED_EXISTENTIAL_ERASED_APPLY_BAD_CPP

#include "small_vector.h"
#include <any>
#include <atomic>
#include <functional>
#include <memory>
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

  static List<A> nil() { return List(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List(Cons{std::move(a), std::make_shared<List<A>>(std::move(l))});
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
    if (std::holds_alternative<typename List<A>::Nil>(this->v())) {
      return UINT64_C(0);
    } else {
      const auto &[a0, a1] = std::get<typename List<A>::Cons>(this->v());
      return (a1->length() + 1);
    }
  }
};

struct ExistentialErasedApplyBadCpp {
  /// dyn packages a value with a consumer for it, hiding the value's type.
  /// The quantified A has no C++ counterpart, so both the value field and
  /// the consumer's argument erase to std::any.
  ///
  /// The consumer is emitted with the erased signature it actually has --
  /// const std::any & in, uint64_t out. For the identity fun k => k the
  /// erased std::any used to be returned directly, with no any_cast back
  /// to the concrete return type:
  ///
  /// (const std::any &k) -> uint64_t { return k; }
  ///
  /// which does not compile. The other two consumers were already fine: they
  /// use their argument at a site with a known expected type (.first, a
  /// method call), which is where the cast was being inserted. A bare return
  /// has no such site, so the lambda's declared return type is now threaded
  /// through as the expected type there.
  struct dyn {
    // DATA
    std::any a;
    std::function<uint64_t(std::any)> a1;

    // ACCESSORS
    dyn clone() const { return {a, a1}; }

    // CREATORS
    static dyn dyn0(std::any a, std::function<uint64_t(std::any)> a1) {
      return {std::move(a), std::move(a1)};
    }
  };

  template <typename T1, typename F0> static T1 dyn_rect(F0 &&f, const dyn &d) {
    const auto &[a0, a1] = d;
    return std::any_cast<T1>(f(a0, a1));
  }

  template <typename T1, typename F0> static T1 dyn_rec(F0 &&f, const dyn &d) {
    const auto &[a0, a1] = d;
    return std::any_cast<T1>(f(a0, a1));
  }

  static uint64_t force(const dyn &d);
  static List<dyn> mk(uint64_t n);
  static uint64_t total(const List<dyn> &l);
  static uint64_t run(uint64_t n);
};

#endif // INCLUDED_EXISTENTIAL_ERASED_APPLY_BAD_CPP
