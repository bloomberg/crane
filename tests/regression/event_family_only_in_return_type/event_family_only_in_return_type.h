#ifndef INCLUDED_EVENT_FAMILY_ONLY_IN_RETURN_TYPE
#define INCLUDED_EVENT_FAMILY_ONLY_IN_RETURN_TYPE

#include "small_vector.h"
#include <any>
#include <atomic>
#include <crane_itree.h>
#include <memory>
#include <stdexcept>
#include <utility>
#include <variant>

struct Nat;
struct Vd;
struct OOME;
struct UBE;

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

struct Vd {
  Vd() = delete;

  std::any vd_elim() const { throw std::logic_error("absurd case"); }
};

struct OOME {
  // DATA
  std::monostate a0;

  // ACCESSORS
  OOME clone() const { return {a0}; }

  // CREATORS
  static OOME throwoom(std::monostate a0) { return {a0}; }
};

struct UBE {
  // TYPES
  struct Throwub {
    std::monostate a0;
  };

  struct Ubread {
    std::monostate a0;
  };

  using variant_t = std::variant<Throwub, Ubread>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  UBE() {}

  explicit UBE(Throwub _v) : v_(std::move(_v)) {}

  explicit UBE(Ubread _v) : v_(std::move(_v)) {}

  static UBE throwub(std::monostate a0) { return UBE(Throwub{a0}); }

  static UBE ubread(std::monostate a0) { return UBE(Ubread{a0}); }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

template <typename T1, typename T2>
std::shared_ptr<ITree<T2>> trigger_cast_(T1 e) {
  return itree_bind(itree_trigger(e),
                    [](const Vd &_x) { return _x.vd_elim(); });
}

struct EventFamilyOnlyInReturnType {
  template <typename T1 = void, typename T2>
  static std::shared_ptr<ITree<T2>> raiseUB() {
    return trigger_cast_<std::any, T2>(UBE::throwub(std::monostate{}));
  }

  static std::shared_ptr<ITree<Nat>> run();
  static std::shared_ptr<ITree<Nat>> run_sum();
};

#endif // INCLUDED_EVENT_FAMILY_ONLY_IN_RETURN_TYPE
