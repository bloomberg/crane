#ifndef INCLUDED_OPTION_RECURSIVE_MATCH
#define INCLUDED_OPTION_RECURSIVE_MATCH

#include "crane_fn.h"
#include "obj.h"
#include "small_vector.h"
#include <atomic>
#include <memory>
#include <stdexcept>
#include <utility>
#include <variant>

struct Nat;
template <typename A> struct Option;

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

template <typename A> struct Option {
  // TYPES
  struct Some {
    A a;
  };

  struct None {};

  using variant_t = std::variant<Some, None>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Option() {}

  explicit Option(Some _v) : v_(std::move(_v)) {}

  explicit Option(None _v) : v_(_v) {}

  template <typename CraneU>
  Option(const Option<CraneU> &_other)
      : v_([&]() -> variant_t {
          if (std::holds_alternative<typename Option<CraneU>::Some>(
                  _other.v())) {
            const auto &[a] =
                std::get<typename Option<CraneU>::Some>(_other.v());
            return Some{[&]() -> A {
              if constexpr (crane_convertible<A, const CraneU &>) {
                return crane_convert<A>(a);
              } else {
                throw std::logic_error("unreachable: inactive constructor "
                                       "field at this instantiation");
              }
            }()};
          } else {
            return None{};
          }
        }()) {}

  static Option<A> some(A a) { return Option<A>(Some{std::move(a)}); }

  static Option<A> none() { return Option<A>(None{}); }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct OptionRecursiveMatch {
  struct chain {
    // TYPES
    struct C {
      Nat a0;
      std::shared_ptr<Option<chain>> a1;
    };

    using variant_t = std::variant<C>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    chain() {}

    explicit chain(C _v) : v_(std::move(_v)) {}

    static chain c(Nat a0, Option<chain> a1) {
      return chain(
          C{std::move(a0), std::make_shared<Option<chain>>(std::move(a1))});
    }

    // MANIPULATORS
    ~chain() {
      crane::small_vector<std::shared_ptr<chain>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<C>(&_v)) {
          if (_alt->a1 && _alt->a1.use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            if (auto *_ha1 = std::get_if<typename Option<chain>::Some>(
                    &(*_alt->a1).v_mut())) {
              _stack.push_back(std::make_shared<chain>(std::move(_ha1->a)));
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

    chain(const chain &) = default;
    chain &operator=(const chain &) = default;
    chain(chain &&) = default;
    chain &operator=(chain &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F0>
  static T1 chain_rect(F0 &&f, const chain &c) {
    const auto &[a0, a1] = std::get<typename chain::C>(c.v());
    return f(a0, *a1);
  }

  template <typename T1, typename F0>
  static T1 chain_rec(F0 &&f, const chain &c) {
    return chain_rect<T1>(f, c);
  }

  static Nat len(const chain &c);
  static inline const Nat test = len(chain::c(
      Nat::s(Nat::o()), Option<chain>::some(chain::c(Nat::s(Nat::s(Nat::o())),
                                                     Option<chain>::none()))));
};

#endif // INCLUDED_OPTION_RECURSIVE_MATCH
