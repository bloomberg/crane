#ifndef INCLUDED_CLASS_FIELD_TYPE_VIA_SECTION_INDUCTIVE
#define INCLUDED_CLASS_FIELD_TYPE_VIA_SECTION_INDUCTIVE

#include "small_vector.h"
#include <any>
#include <atomic>
#include <concepts>
#include <memory>
#include <utility>
#include <variant>

struct Nat;
template <typename ptr, typename iptr> struct Dvalue_base;
struct natParams;
struct natToBase;
using ptr = std::any;
using iptr = std::any;
template <typename
I>concept Params = requires {
  typename I::ptr;
  typename I::iptr;
} && (requires {
  { I::nullp() } -> std::convertible_to<typename I::ptr>;
} || requires {
  { I::nullp } -> std::convertible_to<typename I::ptr>;
}) && (requires {
  { I::zeroi() } -> std::convertible_to<typename I::iptr>;
} || requires {
  { I::zeroi } -> std::convertible_to<typename I::iptr>;
});
/// Takes only I.  Its field's type is the section inductive, so its
/// dependence on Params is never written down.
template <typename _Inst, typename I>
concept ToDvalueBase = requires {
  {
    _Inst::tdb(std::declval<I>())
  } -> std::convertible_to<Dvalue_base<ptr, iptr>>;
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

/// Declared in the section, so discharge parameterises it by ptr and
/// iptr.  This is what carries Params into the class below.
template <typename ptr, typename iptr> struct Dvalue_base {
  // TYPES
  struct DVALUE_Pointer {
    ptr a0;
  };

  struct DVALUE_Iptr {
    iptr a0;
  };

  using variant_t = std::variant<DVALUE_Pointer, DVALUE_Iptr>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Dvalue_base() {}

  explicit Dvalue_base(DVALUE_Pointer _v) : v_(std::move(_v)) {}

  explicit Dvalue_base(DVALUE_Iptr _v) : v_(std::move(_v)) {}

  template <typename _U0, typename _U1>
  Dvalue_base(const Dvalue_base<_U0, _U1> &_other) {
    if (std::holds_alternative<typename Dvalue_base<_U0, _U1>::DVALUE_Pointer>(
            _other.v())) {
      const auto &[a0] =
          std::get<typename Dvalue_base<_U0, _U1>::DVALUE_Pointer>(_other.v());
      this->v_ = DVALUE_Pointer{a0};
    } else {
      const auto &[a0] =
          std::get<typename Dvalue_base<_U0, _U1>::DVALUE_Iptr>(_other.v());
      this->v_ = DVALUE_Iptr{a0};
    }
  }

  static Dvalue_base<ptr, iptr> dvalue_pointer(ptr a0) {
    return Dvalue_base<ptr, iptr>(DVALUE_Pointer{std::move(a0)});
  }

  static Dvalue_base<ptr, iptr> dvalue_iptr(iptr a0) {
    return Dvalue_base<ptr, iptr>(DVALUE_Iptr{std::move(a0)});
  }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

template <typename _tcI0, Params _tcI1, Params _tcI2, typename T1>
  requires ToDvalueBase<_tcI0, T1>
Dvalue_base<typename _tcI1::ptr, typename _tcI1::iptr> to_base(const T1 &x) {
  return _tcI0::tdb(x);
}

struct natParams {
  using ptr = Nat;
  using iptr = Nat;

  static Nat nullp() { return Nat::o(); }

  static Nat zeroi() { return Nat::o(); }
};

static_assert(Params<natParams>);

struct natToBase {
  static Dvalue_base<ptr, iptr> tdb(Nat n) {
    return Dvalue_base<ptr, iptr>::dvalue_iptr(std::move(n));
  }
};

static_assert(ToDvalueBase<natToBase, Nat>);

struct ClassFieldTypeViaSectionInductive {
  static inline const Dvalue_base<typename natParams::ptr,
                                  typename natParams::iptr>
      run = to_base<natToBase, natParams, natParams, Nat>(
          Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::o()))))))));
};

#endif // INCLUDED_CLASS_FIELD_TYPE_VIA_SECTION_INDUCTIVE
