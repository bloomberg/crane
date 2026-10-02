#ifndef INCLUDED_CLASS_FIELD_TYPE_VIA_SECTION_INDUCTIVE
#define INCLUDED_CLASS_FIELD_TYPE_VIA_SECTION_INDUCTIVE

#include "crane_fn.h"
#include "obj.h"
#include <any>
#include <atomic>
#include <concepts>
#include <memory>
#include <stdexcept>
#include <utility>
#include <variant>

struct Nat;
template <typename ptr, typename iptr> struct Dvalue_base;
struct natParams;
struct natToBase;
using ptr = crane::obj;
using iptr = crane::obj;
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
template <typename _Inst, typename I, typename ptr, typename iptr>
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
  Dvalue_base(const Dvalue_base<_U0, _U1> &_other)
      : v_([&]() -> variant_t {
          if (std::holds_alternative<
                  typename Dvalue_base<_U0, _U1>::DVALUE_Pointer>(_other.v())) {
            const auto &[a0] =
                std::get<typename Dvalue_base<_U0, _U1>::DVALUE_Pointer>(
                    _other.v());
            return DVALUE_Pointer{[&]() -> ptr {
              if constexpr (crane_convertible<ptr, const _U0 &>) {
                return crane_convert<ptr>(a0);
              } else {
                throw std::logic_error("unreachable: inactive constructor "
                                       "field at this instantiation");
              }
            }()};
          } else {
            const auto &[a0] =
                std::get<typename Dvalue_base<_U0, _U1>::DVALUE_Iptr>(
                    _other.v());
            return DVALUE_Iptr{[&]() -> iptr {
              if constexpr (crane_convertible<iptr, const _U1 &>) {
                return crane_convert<iptr>(a0);
              } else {
                throw std::logic_error("unreachable: inactive constructor "
                                       "field at this instantiation");
              }
            }()};
          }
        }()) {}

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
  requires ToDvalueBase<_tcI0, T1, typename _tcI1::ptr, typename _tcI1::iptr>
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
  static Dvalue_base<typename natParams::ptr, typename natParams::iptr>
  tdb(Nat n) {
    return Dvalue_base<typename natParams::ptr,
                       typename natParams::iptr>::dvalue_iptr(std::move(n));
  }
};

static_assert(ToDvalueBase<natToBase, Nat, typename natParams::ptr,
                           typename natParams::iptr>);

struct ClassFieldTypeViaSectionInductive {
  static inline const Dvalue_base<typename natParams::ptr,
                                  typename natParams::iptr>
      run = to_base<natToBase, natParams, natParams, Nat>(
          Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::o()))))))));
};

#endif // INCLUDED_CLASS_FIELD_TYPE_VIA_SECTION_INDUCTIVE
