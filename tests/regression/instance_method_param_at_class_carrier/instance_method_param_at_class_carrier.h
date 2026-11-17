#ifndef INCLUDED_INSTANCE_METHOD_PARAM_AT_CLASS_CARRIER
#define INCLUDED_INSTANCE_METHOD_PARAM_AT_CLASS_CARRIER

#include "obj.h"
#include <atomic>
#include <concepts>
#include <memory>
#include <utility>
#include <variant>

struct Nat;
struct natCarrier;
using carr = crane::obj;
template <typename I>
concept Carrier = requires {
  typename I::carr;
  { I::render(std::declval<typename I::carr>()) } -> std::convertible_to<Nat>;
};
template <typename I, typename A>
concept Show = requires {
  { I::show(std::declval<A>()) } -> std::convertible_to<Nat>;
};

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

template <Carrier _tcI0> struct showCarr {
  using carr = typename _tcI0::carr;

  static Nat show(typename _tcI0::carr a0) {
    return _tcI0::render(std::move(a0));
  }
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
