#ifndef INCLUDED_ITREE_POLY_EVENT_ARG
#define INCLUDED_ITREE_POLY_EVENT_ARG

#include <atomic>
#include <crane_itree.h>
#include <memory>
#include <utility>
#include <variant>

struct Nat;

struct ItreePolyEventArg {
  static std::shared_ptr<ITree<Nat>> use(const Nat &n);
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
  Nat(Nat &&) noexcept = default;
  Nat &operator=(Nat &&) noexcept = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

template <typename T1 = void>
std::shared_ptr<ITree<Nat>> f(const std::shared_ptr<ITree<Nat>> &x) {
  return itree_bind(x, [](const Nat &a) { return itree_ret(Nat::s(a)); });
}

#endif // INCLUDED_ITREE_POLY_EVENT_ARG
