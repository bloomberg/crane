#ifndef INCLUDED_SUBEVENT_INSTANCE_DROPPED
#define INCLUDED_SUBEVENT_INSTANCE_DROPPED

#include "small_vector.h"
#include <atomic>
#include <crane_itree.h>
#include <memory>
#include <stdexcept>
#include <utility>
#include <variant>

struct Empty_set;
struct Nat;
struct FailE;

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

struct FailE {
  // DATA
  Nat a0;

  // ACCESSORS
  FailE clone() const { return {a0}; }

  // CREATORS
  static FailE fail(Nat a0) { return {std::move(a0)}; }
};

template <template <typename> class T1, typename T2 = void, typename T3>
std::shared_ptr<ITree<T3>> cast(T1<T3> e) {
  return itree_trigger(e);
}

template <typename T1, typename T2> std::shared_ptr<ITree<T2>> boom(Nat n) {
  return itree_bind(
      [=]() mutable -> std::shared_ptr<ITree<Empty_set>> {
        return ITree<Empty_set>::ret(
            cast<FailE, T1, Empty_set>(FailE::fail(std::move(n))));
      }(),
      [](const auto &) { throw std::logic_error("absurd case"); });
}

struct SubeventInstanceDropped {
  static std::shared_ptr<ITree<Nat>> use(const Nat &n);
};

#endif // INCLUDED_SUBEVENT_INSTANCE_DROPPED
