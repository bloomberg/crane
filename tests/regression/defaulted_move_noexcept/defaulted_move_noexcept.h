#ifndef INCLUDED_DEFAULTED_MOVE_NOEXCEPT
#define INCLUDED_DEFAULTED_MOVE_NOEXCEPT

#include "crane_fn.h"
#include "obj.h"
#include <atomic>
#include <memory>
#include <stdexcept>
#include <utility>
#include <variant>

struct Nat;

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
  Nat(Nat &&) = default;
  Nat &operator=(Nat &&) = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct DefaultedMoveNoexcept {
  /// A recursive datatype gets a user-declared destructor, and so re-defaulted
  /// moves.  Their exception specification is inferred: noexcept exactly
  /// when moving the payload is.
  template <typename A> struct seq {
    // TYPES
    struct Nil {};

    struct Cons {
      A a;
      std::shared_ptr<seq<A>> s;
    };

    using variant_t = std::variant<Nil, Cons>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    seq() {}

    explicit seq(Nil _v) : v_(_v) {}

    explicit seq(Cons _v) : v_(std::move(_v)) {}

    template <typename CraneU>
    seq(const seq<CraneU> &_other)
        : v_([&]() -> variant_t {
            if (std::holds_alternative<typename seq<CraneU>::Nil>(_other.v())) {
              return Nil{};
            } else {
              const auto &[a, s] =
                  std::get<typename seq<CraneU>::Cons>(_other.v());
              return Cons{
                  [&]() -> A {
                    if constexpr (crane_convertible<A, const CraneU &>) {
                      return crane_convert<A>(a);
                    } else {
                      throw std::logic_error(
                          "unreachable: inactive constructor field at this "
                          "instantiation");
                    }
                  }(),
                  (s ? std::make_shared<seq<A>>(crane_convert<seq<A>>(*s))
                     : nullptr)};
            }
          }()) {}

    static seq<A> nil() { return seq<A>(Nil{}); }

    static seq<A> cons(A a, seq<A> s) {
      return seq<A>(Cons{std::move(a), std::make_shared<seq<A>>(std::move(s))});
    }

    // MANIPULATORS
    ~seq() {
      auto _next = [&](variant_t &_v) -> std::shared_ptr<seq<A>> {
        if (auto *_alt = std::get_if<Cons>(&_v)) {
          if (_alt->s && _alt->s.use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            return std::move(_alt->s);
          }
        }
        return nullptr;
      };
      std::shared_ptr<seq<A>> _cur = _next(v_mut());
      while (_cur) {
        _cur = _next(_cur->v_mut());
      }
    }

    seq(const seq &) = default;
    seq &operator=(const seq &) = default;
    seq(seq &&) = default;
    seq &operator=(seq &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename T2, typename F1>
  static T2 seq_rect(T2 f, F1 &&f0, const seq<T1> &s) {
    if (std::holds_alternative<typename seq<T1>::Nil>(s.v())) {
      return f;
    } else {
      const auto &[a0, s1] = std::get<typename seq<T1>::Cons>(s.v());
      return f0(a0, *s1, seq_rect<T1, T2>(std::move(f), f0, *s1));
    }
  }

  template <typename T1, typename T2, typename F1>
  static T2 seq_rec(T2 f, F1 &&f0, const seq<T1> &s) {
    return seq_rect<T1, T2>(std::move(f), f0, s);
  }

  template <typename T1> static Nat len(const seq<T1> &s) {
    if (std::holds_alternative<typename seq<T1>::Nil>(s.v())) {
      return Nat::o();
    } else {
      const auto &[a, s0] = std::get<typename seq<T1>::Cons>(s.v());
      return Nat::s(len<T1>(*s0));
    }
  }
};

#endif // INCLUDED_DEFAULTED_MOVE_NOEXCEPT
