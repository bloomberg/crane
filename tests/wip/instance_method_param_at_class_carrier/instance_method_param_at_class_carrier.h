#ifndef INCLUDED_INSTANCE_METHOD_PARAM_AT_CLASS_CARRIER
#define INCLUDED_INSTANCE_METHOD_PARAM_AT_CLASS_CARRIER

#include "small_vector.h"
#include <any>
#include <atomic>
#include <concepts>
#include <memory>
#include <utility>
#include <variant>

struct Nat;
struct natCarrier;

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
concept Carrier = requires {
  typename I::carr;
  { I::render(std::declval<typename I::carr>()) } -> std::convertible_to<Nat>;
};
using carr = std::any;
template <typename I, typename A>
concept Show = requires {
  { I::show(std::declval<A>()) } -> std::convertible_to<Nat>;
};

template <Carrier _tcI0> struct showCarr {
  using carr = typename _tcI0::carr;

  static Nat show(std::any a0) { return _tcI0::render(a0); }
};

template <Carrier _tcI0> Nat describe(const typename _tcI0::carr &x) {
  return showCarr<_tcI0>::show(x);
}

struct natCarrier {
  using carr = Nat;

  static Nat render(Nat n) { return n; }
};

static_assert(Carrier<natCarrier>);

struct InstanceMethodParamAtClassCarrier {
  static inline const Nat run = describe<natCarrier>(
      Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::o()))))))));
};

#endif // INCLUDED_INSTANCE_METHOD_PARAM_AT_CLASS_CARRIER
