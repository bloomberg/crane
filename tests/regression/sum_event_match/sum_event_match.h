#ifndef INCLUDED_SUM_EVENT_MATCH
#define INCLUDED_SUM_EVENT_MATCH

#include "small_vector.h"
#include <atomic>
#include <crane_itree.h>
#include <memory>
#include <utility>
#include <variant>

struct Nat;
enum class AE;
enum class BE;

struct SumEventMatch {
  static std::shared_ptr<ITree<Nat>> use();
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
enum class AE { A0 };
enum class BE { B0 };

template <typename T1>
std::shared_ptr<ITree<T1>> handle(const Sum1<AE, BE, T1> &e) {
  if (std::holds_alternative<typename Sum1<AE, BE, T1>::Inl1>(e.v())) {
    const auto &[a0] = std::get<typename Sum1<AE, BE, T1>::Inl1>(e.v());
    return itree_trigger(sum1_inl(a0));
  } else {
    const auto &[a0] = std::get<typename Sum1<AE, BE, T1>::Inr1>(e.v());
    return itree_trigger(sum1_inr(a0));
  }
}

#endif // INCLUDED_SUM_EVENT_MATCH
