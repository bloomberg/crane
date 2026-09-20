#ifndef INCLUDED_APPLIED_TYPENAME_NOT_HK
#define INCLUDED_APPLIED_TYPENAME_NOT_HK

#include "small_vector.h"
#include <any>
#include <atomic>
#include <crane_itree.h>
#include <memory>
#include <utility>
#include <variant>

struct Nat;
struct AE;

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

struct AE {
  // DATA
  Nat a0_0;

  // ACCESSORS
  AE clone() const { return {a0_0}; }

  // CREATORS
  static AE a0(Nat a0_0) { return {std::move(a0_0)}; }

  std::shared_ptr<ITree<std::any>> handle() const {
    const auto &[a0] = *this;
    return crane_container_cast<std::shared_ptr<ITree<std::any>>>(
        itree_ret(a0));
  }
};

template <typename T1, typename T2 = void>
std::shared_ptr<ITree<std::any>> E_trigger(T1 e) {
  return itree_trigger(e);
}

template <typename T1 = void, typename T2>
std::shared_ptr<ITree<std::any>> F_trigger(T2 e) {
  return itree_trigger(e);
}

template <typename T1 = void, typename T2 = void>
std::shared_ptr<ITree<std::any>>
h(Sum1<std::any, Sum1<AE, std::any, std::any>, std::any> x) {
  return itree_case(E_trigger<std::any, std::any>,
                    itree_case([](const auto &_x) { return _x.handle(); },
                               F_trigger<std::any, std::any>))(std::move(x));
}

struct AppliedTypenameNotHk {
  static std::shared_ptr<ITree<Nat>> use(Nat n);
};

#endif // INCLUDED_APPLIED_TYPENAME_NOT_HK
