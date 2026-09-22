#ifndef INCLUDED_NESTED_OWNER_TWO_TEMPLATE_HEADS
#define INCLUDED_NESTED_OWNER_TWO_TEMPLATE_HEADS

#include "crane_fn.h"
#include "small_vector.h"
#include <any>
#include <atomic>
#include <memory>
#include <stdexcept>
#include <type_traits>
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
    crane::small_vector<std::shared_ptr<Nat>> _stack = {};
    auto _drain = [&](variant_t &_v) {
      if (auto *_alt = std::get_if<S>(&_v)) {
        if (_alt->a0) {
          _stack.push_back(std::move(_alt->a0));
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

  Nat(const Nat &) = default;
  Nat &operator=(const Nat &) = default;
  Nat(Nat &&) noexcept = default;
  Nat &operator=(Nat &&) noexcept = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct Bag {
  template <typename A> struct bag {
    // TYPES
    struct Empty {};

    struct Add {
      A a0;
      std::shared_ptr<typename Bag::template bag<A>> a1;
    };

    using variant_t = std::variant<Empty, Add>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    bag() {}

    explicit bag(Empty _v) : v_(_v) {}

    explicit bag(Add _v) : v_(std::move(_v)) {}

    template <typename _U> bag(const typename Bag::template bag<_U> &_other) {
      if (std::holds_alternative<typename Bag::template bag<_U>::Empty>(
              _other.v())) {
        this->v_ = Empty{};
      } else {
        const auto &[a0, a1] =
            std::get<typename Bag::template bag<_U>::Add>(_other.v());
        this->v_ =
            Add{[&]() -> A {
                  if constexpr (crane_convertible<A, const _U &>) {
                    return crane_convert<A>(a0);
                  } else {
                    throw std::logic_error("unreachable: inactive constructor "
                                           "field at this instantiation");
                  }
                }(),
                (a1 ? std::make_shared<typename Bag::template bag<A>>(
                          crane_convert<typename Bag::template bag<A>>(*a1))
                    : nullptr)};
      }
    }

    static typename Bag::template bag<A> empty() {
      return typename Bag::template bag<A>(Empty{});
    }

    static typename Bag::template bag<A> add(A a0, Bag::bag<A> a1) {
      return typename Bag::template bag<A>(
          Add{std::move(a0),
              std::make_shared<typename Bag::template bag<A>>(std::move(a1))});
    }

    // MANIPULATORS
    ~bag() {
      crane::small_vector<std::shared_ptr<typename Bag::template bag<A>>>
          _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<Add>(&_v)) {
          if (_alt->a1) {
            _stack.push_back(std::move(_alt->a1));
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

    bag(const bag &) = default;
    bag &operator=(const bag &) = default;
    bag(bag &&) noexcept = default;
    bag &operator=(bag &&) noexcept = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    template <typename F0>
      requires std::is_invocable_r_v<bool, F0 &, A &>
    Nat countIf(F0 &&p) const;
  };

  static inline const Nat depth_limit =
      Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::o()))))))));
};

struct PeanoNat {
  static bool eqb(const Nat &n, const Nat &m);
  static bool even(const Nat &n);
  static bool odd(const Nat &n);
};

struct Tally {
  struct held {
    Bag::bag<Nat> unhold;
  };

  static Nat bump(Nat n);
};

Bag::bag<Nat> roundtrip(Bag::bag<Nat> b);
bool count_odd_is(const Bag::bag<Nat> &b, const Nat &n);
const Nat limit = Bag::depth_limit;
Bag::bag<Nat> round(const Bag::bag<Nat> &x0_);

template <typename A>
template <typename F0>
  requires std::is_invocable_r_v<bool, F0 &, A &>
Nat Bag::bag<A>::countIf(F0 &&p) const {
  if (std::holds_alternative<typename Bag::bag<A>::Empty>(this->v())) {
    return Nat::o();
  } else {
    const auto &[a0, a1] = std::get<typename Bag::bag<A>::Add>(this->v());
    if (p(a0)) {
      return Tally::bump(a1->countIf(p));
    } else {
      return a1->countIf(p);
    }
  }
}

#endif // INCLUDED_NESTED_OWNER_TWO_TEMPLATE_HEADS
