#ifndef INCLUDED_SKIPPED_DICT_FAMILY_UNCONSTRAINED
#define INCLUDED_SKIPPED_DICT_FAMILY_UNCONSTRAINED

#include "obj.h"
#include <any>
#include <atomic>
#include <crane_itree.h>
#include <memory>
#include <stdexcept>
#include <utility>
#include <variant>

struct Nat;
struct Void0;
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

struct Void0 {
  Void0() = delete;

  crane::obj void_elim() const { throw std::logic_error("absurd case"); }
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
std::shared_ptr<ITree<T2>> trigger_cast_(crane::rebind_t<T1, Void0> e) {
  return itree_bind(itree_trigger(e),
                    [](const Void0 &_x) { return _x.void_elim(); });
}

struct SkippedDictFamilyUnconstrained {
  template <typename T1 = void, typename T2>
  static std::shared_ptr<ITree<T2>> raiseUB() {
    return trigger_cast_<crane::obj, T2>(UBE::throwub(std::monostate{}));
  }

  static std::shared_ptr<ITree<Nat>> run();
};

#endif // INCLUDED_SKIPPED_DICT_FAMILY_UNCONSTRAINED
