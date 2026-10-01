#ifndef INCLUDED_SUBEVENT_INSTANCE_DROPPED
#define INCLUDED_SUBEVENT_INSTANCE_DROPPED

#include "obj.h"
#include <any>
#include <atomic>
#include <crane_itree.h>
#include <memory>
#include <stdexcept>
#include <utility>
#include <variant>

struct Empty_set;
struct Nat;
struct FailE;

struct SubeventInstanceDropped {
  static std::shared_ptr<ITree<Nat>> use(const Nat &n);
};

struct Empty_set {
  Empty_set() = delete;
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

struct FailE {
  // DATA
  Nat a0;

  // ACCESSORS
  FailE clone() const { return {a0}; }

  // CREATORS
  static FailE fail(Nat a0) { return {std::move(a0)}; }
};

template <typename T1 = void, typename T2 = void, typename T3, typename _P0>
std::shared_ptr<ITree<T3>> cast(_P0 e) {
  return itree_trigger(e);
}

template <typename T1 = void, typename T2>
std::shared_ptr<ITree<T2>> boom(const Nat &n) {
  return itree_bind(cast<void, crane::obj, Empty_set>(FailE::fail(n)),
                    [](Empty_set) -> std::shared_ptr<ITree<T2>> {
                      throw std::logic_error("absurd case");
                    });
}

#endif // INCLUDED_SUBEVENT_INSTANCE_DROPPED
