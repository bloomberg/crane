#ifndef INCLUDED_CLASS_VALUE_CTOR_DROPS_PROMOTED
#define INCLUDED_CLASS_VALUE_CTOR_DROPS_PROMOTED

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include <atomic>
#include <concepts>
#include <memory>
#include <stdexcept>
#include <utility>
#include <variant>

struct Nat;
template <typename ptr, typename iptr> struct Dvalue_base;
template <typename ptr, typename iptr, typename I> struct ToDvalueBase;
struct natParams;
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
  Nat(Nat &&) = default;
  Nat &operator=(Nat &&) = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

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

  template <typename CraneU0, typename CraneU1>
  Dvalue_base(const Dvalue_base<CraneU0, CraneU1> &_other)
      : v_([&]() -> variant_t {
          if (std::holds_alternative<
                  typename Dvalue_base<CraneU0, CraneU1>::DVALUE_Pointer>(
                  _other.v())) {
            const auto &[a0] = std::get<
                typename Dvalue_base<CraneU0, CraneU1>::DVALUE_Pointer>(
                _other.v());
            return DVALUE_Pointer{[&]() -> ptr {
              if constexpr (crane_convertible<ptr, const CraneU0 &>) {
                return crane_convert<ptr>(a0);
              } else {
                throw std::logic_error("unreachable: inactive constructor "
                                       "field at this instantiation");
              }
            }()};
          } else {
            const auto &[a0] =
                std::get<typename Dvalue_base<CraneU0, CraneU1>::DVALUE_Iptr>(
                    _other.v());
            return DVALUE_Iptr{[&]() -> iptr {
              if constexpr (crane_convertible<iptr, const CraneU1 &>) {
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

template <typename ptr, typename iptr, typename I> struct ToDvalueBase {
  crane::fn<Dvalue_base<ptr, iptr>(I)> tdb;

  // ACCESSORS
  template <typename CraneU> operator ToDvalueBase<ptr, iptr, CraneU>() const {
    return {crane_convert<crane::fn<Dvalue_base<ptr, iptr>(CraneU)>>(tdb)};
  }
};

struct natParams {
  using ptr = Nat;
  using iptr = Nat;

  static Nat nullp() { return Nat::o(); }

  static Nat zeroi() { return Nat::o(); }
};

static_assert(Params<natParams>);

/// Built and returned, so the class is data here and the struct is
/// constructed in an expression position.
template <Params _tcI0, typename T1, typename F0>
ToDvalueBase<typename _tcI0::ptr, typename _tcI0::iptr, T1> mk_to_base(F0 &&f) {
  return ToDvalueBase<typename _tcI0::ptr, typename _tcI0::iptr, T1>{f};
}

template <Params _tcI0, typename T1>
Dvalue_base<typename _tcI0::ptr, typename _tcI0::iptr> apply_to_base(
    const ToDvalueBase<typename _tcI0::ptr, typename _tcI0::iptr, T1> &d,
    const T1 &x) {
  return d.tdb(x);
}

struct ClassValueCtorDropsPromoted {
  static inline const Dvalue_base<typename natParams::ptr,
                                  typename natParams::iptr>
      run = apply_to_base<natParams, Nat>(
          mk_to_base<natParams, Nat>([](const Nat &n) {
            return Dvalue_base<Nat, Nat>::dvalue_iptr(n);
          }),
          Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::o()))))))));
};

#endif // INCLUDED_CLASS_VALUE_CTOR_DROPS_PROMOTED
