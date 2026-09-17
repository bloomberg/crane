#ifndef INCLUDED_MEMBER_ALIAS_AS_TT_ARG
#define INCLUDED_MEMBER_ALIAS_AS_TT_ARG

#include "small_vector.h"
#include <any>
#include <atomic>
#include <concepts>
#include <functional>
#include <memory>
#include <optional>
#include <utility>
#include <variant>

struct Monad_option;
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

template <typename I>
concept Monad = requires {
  typename I::template m<std::any>;
  {
    I::ret(std::declval<std::any>())
  } -> std::convertible_to<typename I::template m<std::any>>;
  {
    I::bind(std::declval<typename I::template m<std::any>>(),
            std::declval<
                std::function<typename I::template m<std::any>(std::any)>>())
  } -> std::convertible_to<typename I::template m<std::any>>;
};

struct Monad_option {
  template <typename _A0> using m = std::optional<_A0>;

  static std::optional<std::any> ret(std::any x) {
    return std::make_optional<std::any>(x);
  }

  static std::optional<std::any>
  bind(std::optional<std::any> c1,
       std::function<std::optional<std::any>(std::any)> c2) {
    if (c1.has_value()) {
      const std::any &v = *c1;
      return c2(v);
    } else {
      return std::optional<std::any>();
    }
  }
};

static_assert(Monad<Monad_option>);
template <typename s, template <typename> class m, typename a>
using stateT = std::function<m<std::pair<a, s>>(s)>;

template <Monad _tcI0, typename T2>
typename _tcI0::template m<std::pair<Nat, T2>>
run(stateT<T2, _tcI0::template m, Nat> step, const T2 &s) {
  return step(s);
}

struct MemberAliasAsTtArg {
  static std::optional<std::pair<Nat, Nat>> use(const Nat &o);
};

#endif // INCLUDED_MEMBER_ALIAS_AS_TT_ARG
