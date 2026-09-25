#ifndef INCLUDED_PARTIAL_APP_ALIAS_VALUE_SLOT
#define INCLUDED_PARTIAL_APP_ALIAS_VALUE_SLOT

#include "small_vector.h"
#include <any>
#include <atomic>
#include <concepts>
#include <crane_itree.h>
#include <memory>
#include <utility>
#include <variant>

struct Nat;
template <typename iptr> struct Dval;
template <typename iptr> struct TopE;
struct natIPtr;

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

template <typename
I>concept IPtr = requires {
  typename I::iptr;
} && (requires {
  { I::zero_iptr() } -> std::convertible_to<typename I::iptr>;
} || requires {
  { I::zero_iptr } -> std::convertible_to<typename I::iptr>;
});
using iptr = std::any;

template <typename iptr> struct Dval {
  // DATA
  iptr i;

  // ACCESSORS
  Dval<iptr> clone() const { return {i}; }

  template <typename _U> operator Dval<_U>() const { return {i}; }

  // CREATORS
  static Dval<iptr> diptr(iptr i) { return {std::move(i)}; }
};

template <typename iptr> struct TopE {
  // DATA
  Dval<iptr> a0;

  // ACCESSORS
  TopE<iptr> clone() const { return {a0}; }

  template <typename _U> operator TopE<_U>() const { return {a0}; }

  // CREATORS
  static TopE<iptr> fail(Dval<iptr> a0) { return {std::move(a0)}; }
};

template <typename iptr, typename r> using Top = std::shared_ptr<ITree<r>>;

template <IPtr _tcI0>
Top<typename _tcI0::iptr, Dval<typename _tcI0::iptr>> seed() {
  return itree_ret(Dval<typename _tcI0::iptr>::diptr(_tcI0::zero_iptr()));
}

struct natIPtr {
  using iptr = Nat;

  static Nat zero_iptr() { return Nat::o(); }
};

static_assert(IPtr<natIPtr>);

struct PartialAppAliasValueSlot {
  static inline const Top<typename natIPtr::iptr, Dval<typename natIPtr::iptr>>
      go = seed<natIPtr>();
};

#endif // INCLUDED_PARTIAL_APP_ALIAS_VALUE_SLOT
