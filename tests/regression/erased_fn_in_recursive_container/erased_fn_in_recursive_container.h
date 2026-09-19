#ifndef INCLUDED_ERASED_FN_IN_RECURSIVE_CONTAINER
#define INCLUDED_ERASED_FN_IN_RECURSIVE_CONTAINER

#include "crane_fn.h"
#include "small_vector.h"
#include <any>
#include <atomic>
#include <functional>
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

  template <typename _U> List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      this->v_ = Nil{};
    } else {
      const auto &[a, l] = std::get<typename List<_U>::Cons>(_other.v());
      this->v_ =
          Cons{[&]() -> A {
                 if constexpr (std::is_same_v<_U, std::any>) {
                   return crane_any_cast<A>(a);
                 } else {
                   if constexpr (std::is_constructible_v<A, const _U &>) {
                     return A(a);
                   } else {
                     throw std::logic_error("unreachable: inactive constructor "
                                            "field at this instantiation");
                   }
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
};

/// The payload of a recursive polymorphic container is erased to std::any on
/// the way in, but the read back at option (nat -> nat) is spelled as a
/// plain functional cast rather than an unerasing one: "no matching conversion
/// for functional-style cast from 'const std::function<std::any (std::any)>'
/// to 'std::function<Nat (Nat)>'".  The same payload in a non-recursive
/// container round-trips correctly.
struct ErasedFnInRecursiveContainer {
  template <typename A> struct rose {
    // TYPES
    struct Node {
      A a0;
      std::shared_ptr<List<rose<A>>> a1;
    };

    using variant_t = std::variant<Node>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    rose() {}

    explicit rose(Node _v) : v_(std::move(_v)) {}

    template <typename _U> rose(const rose<_U> &_other) {
      const auto &[a0, a1] = std::get<typename rose<_U>::Node>(_other.v());
      this->v_ =
          Node{[&]() -> A {
                 if constexpr (std::is_same_v<_U, std::any>) {
                   return crane_any_cast<A>(a0);
                 } else {
                   if constexpr (std::is_constructible_v<A, const _U &>) {
                     return A(a0);
                   } else {
                     throw std::logic_error("unreachable: inactive constructor "
                                            "field at this instantiation");
                   }
                 }
               }(),
               (a1 ? std::make_shared<List<rose<A>>>(*a1) : nullptr)};
    }

    static rose<A> node(A a0, List<rose<A>> a1) {
      return rose<A>(
          Node{std::move(a0), std::make_shared<List<rose<A>>>(std::move(a1))});
    }

    // MANIPULATORS
    ~rose() {
      crane::small_vector<std::shared_ptr<rose<A>>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<Node>(&_v)) {
          if (_alt->a1 && _alt->a1.use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            auto _lp = _alt->a1.get();
            while (std::holds_alternative<typename List<rose<A>>::Cons>(
                _lp->v())) {
              auto &_lc = std::get<typename List<rose<A>>::Cons>(_lp->v_mut());
              _stack.push_back(std::make_shared<rose<A>>(std::move(_lc.a)));
              if (_lc.l && _lc.l.use_count() == 1) {
                std::atomic_thread_fence(std::memory_order_acquire);
                _lp = _lc.l.get();
              } else {
                break;
              }
            }
            _alt->a1.reset();
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

    rose(const rose &) = default;
    rose &operator=(const rose &) = default;
    rose(rose &&) noexcept = default;
    rose &operator=(rose &&) noexcept = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename T2, typename F0>
    requires std::is_invocable_r_v<T2, F0 &, T1 &, List<rose<T1>> &>
  static T2 rose_rect(F0 &&f, const rose<T1> &r) {
    const auto &[a0, a1] = std::get<typename rose<T1>::Node>(r.v());
    return f(a0, *a1);
  }

  template <typename T1, typename T2, typename F0>
    requires std::is_invocable_r_v<T2, F0 &, T1 &, List<rose<T1>> &>
  static T2 rose_rec(F0 &&f, const rose<T1> &r) {
    const auto &[a0, a1] = std::get<typename rose<T1>::Node>(r.v());
    return f(a0, *a1);
  }

  template <typename T1> static uint64_t size(const rose<T1> &x) {
    const auto &[a0, a1] = std::get<typename rose<T1>::Node>(x.v());
    const List<rose<T1>> &a1_value = *a1;
    return (a1_value.template fold_left<uint64_t>(
                [](uint64_t a, const rose<T1> &y) { return (a + size<T1>(y)); },
                UINT64_C(0)) +
            1);
  }

  static inline const uint64_t run = size<
      std::optional<std::function<uint64_t(uint64_t)>>>(
      rose<std::optional<std::function<uint64_t(uint64_t)>>>::node(
          std::make_optional<std::function<uint64_t(uint64_t)>>(
              [](const auto &x) { return x; }),
          List<rose<std::optional<std::function<uint64_t(uint64_t)>>>>::cons(
              rose<std::optional<std::function<uint64_t(uint64_t)>>>::node(
                  std::optional<std::function<uint64_t(uint64_t)>>(),
                  List<rose<std::optional<std::function<uint64_t(uint64_t)>>>>::
                      nil()),
              List<rose<std::optional<std::function<uint64_t(uint64_t)>>>>::
                  nil())));
};

#endif // INCLUDED_ERASED_FN_IN_RECURSIVE_CONTAINER
