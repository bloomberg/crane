#ifndef INCLUDED_NESTED_INSTANCE_FIELD_RESOLUTION
#define INCLUDED_NESTED_INSTANCE_FIELD_RESOLUTION

#include <any>
#include <atomic>
#include <concepts>
#include <memory>
#include <stdexcept>
#include <utility>
#include <variant>
#include <crane_itree.h>
#include <utility>
#include "fn.h"
#include "obj.h"
#include "crane_fn.h"





struct Nat;
template <typename A>struct EOU;
struct EOU_monad;
template <typename ptr, typename iptr, typename
ADDR>struct Dval;
struct natIPtr;
struct ProvenanceV;
struct PointerV;using iptr = crane::obj;
using ptr = crane::obj;
using ADDR = crane::obj;template <typename
I>concept Monad = requires {
    typename I::template m<crane::obj>;
    { I::template ret<crane::obj>(std::declval<crane::obj>()) } -> std::convertible_to<typename I::template m<crane::obj>>;
    { I::bind(std::declval<typename I::template m<crane::obj>>(), std::declval<crane::fn<typename I::template m<crane::obj>(crane::obj)>>()) } -> std::convertible_to<typename I::template m<crane::obj>>;
  };template <typename
I>concept IPtr = requires {
    typename I::iptr;
    { I::from_Z(std::declval<Nat>()) } -> std::convertible_to<EOU<typename I::iptr>>;
    { I::to_Z(std::declval<typename I::iptr>()) } -> std::convertible_to<Nat>;
  } && (requires {
    { I::zero_iptr() } -> std::convertible_to<typename I::iptr>;
  } || requires {
    { I::zero_iptr } -> std::convertible_to<typename I::iptr>;
  });template <typename
I>concept Provenance = requires {
    typename I::prov;
  } && (requires {
    { I::nil_prov() } -> std::convertible_to<typename I::prov>;
  } || requires {
    { I::nil_prov } -> std::convertible_to<typename I::prov>;
  });template <typename
I>concept Pointer = requires {
    typename I::ptr;
  } && (requires {
    { I::null() } -> std::convertible_to<typename I::ptr>;
  } || requires {
    { I::null } -> std::convertible_to<typename I::ptr>;
  });template <typename
I>concept Params = requires {
    typename I::ADDR;
    typename I::PROV;
    typename I::PTR;
    typename I::IPTR;
  } && (requires {
    { I::zero_addr() } -> std::convertible_to<typename I::ADDR>;
  } || requires {
    { I::zero_addr } -> std::convertible_to<typename I::ADDR>;
  });
struct Nat {
  // TYPES
struct O {

};
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
static Nat o() {
return Nat(O{});}
static Nat s(Nat a0) {
return Nat(S{std::make_shared<Nat>(std::move(a0))});}
  // MANIPULATORS
~Nat() {
auto _next = [&](variant_t& _v) -> std::shared_ptr<Nat> {
if (auto* _alt = std::get_if<S>(&_v)) {
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
Nat(const Nat&) = default;
Nat& operator=(const Nat&) = default;
Nat(Nat&&) noexcept = default;
Nat& operator=(Nat&&) noexcept = default;
inline variant_t& v_mut() {
return v_;}
  // ACCESSORS
const variant_t& v() const {
return v_;}
};template <typename
A>struct EOU {
  // TYPES
struct Ok {
A a0;
};
struct Err {
Nat a0;
};
using variant_t = std::variant<Ok, Err>;
private:
  // DATA
variant_t v_;
public:
  // CREATORS
EOU() {}
explicit EOU(Ok _v) : v_(std::move(_v)) {}
explicit EOU(Err _v) : v_(std::move(_v)) {}
template <typename
_U>
EOU(const EOU<_U>& _other) : v_([&]() -> variant_t {
if (std::holds_alternative<typename EOU<_U>::Ok>(_other.v())) {
const auto& [a0] = std::get<typename EOU<_U>::Ok>(_other.v());
return Ok{[&]() -> A {
if constexpr (crane_convertible<A, const _U&>) {
return crane_convert<A>(a0);
} else {
throw std::logic_error("unreachable: inactive constructor field at this instantiation");
}
}()};
} else {
const auto& [a0] = std::get<typename EOU<_U>::Err>(_other.v());
return Err{a0};
}
}()) {}
static EOU<A> ok(A a0) {
return EOU<A>(Ok{std::move(a0)});}
static EOU<A> err(Nat a0) {
return EOU<A>(Err{std::move(a0)});}
  // MANIPULATORS
inline variant_t& v_mut() {
return v_;}
  // ACCESSORS
const variant_t& v() const {
return v_;}
};
struct EOU_monad {
template <typename _A0> using m = EOU<_A0>;
template <typename
_A0>
static EOU<_A0> ret(_A0 a) {
return EOU<_A0>::ok(std::move(a));}
static EOU<crane::obj> bind(EOU<crane::obj> m, crane::fn<EOU<crane::obj>(crane::obj)> k) {
if (std::holds_alternative<typename EOU<crane::obj>::Ok>(m.v())) {
const auto& [a0] = std::get<typename EOU<crane::obj>::Ok>(m.v());
return k(a0);
} else {
const auto& [a0] = std::get<typename EOU<crane::obj>::Err>(m.v());
return EOU<crane::obj>::err(a0);
}}
};
static_assert(Monad<EOU_monad>);template <typename ptr, typename iptr,
typename
ADDR>struct Dval {
  // TYPES
struct DPtr {
ptr p;
};
struct DIptr {
iptr i;
};
struct DAddr {
ADDR a;
};
using variant_t = std::variant<DPtr, DIptr, DAddr>;
private:
  // DATA
variant_t v_;
public:
  // CREATORS
Dval() {}
explicit Dval(DPtr _v) : v_(std::move(_v)) {}
explicit Dval(DIptr _v) : v_(std::move(_v)) {}
explicit Dval(DAddr _v) : v_(std::move(_v)) {}
template <typename _U0, typename _U1, typename _U2>
Dval(const Dval<_U0, _U1,
_U2>& _other) : v_([&]() -> variant_t {
if (std::holds_alternative<typename Dval<_U0, _U1,
_U2>::DPtr>(_other.v())) {
const auto& [p] = std::get<typename Dval<_U0, _U1,
_U2>::DPtr>(_other.v());
return DPtr{[&]() -> ptr {
if constexpr (crane_convertible<ptr, const _U0&>) {
return crane_convert<ptr>(p);
} else {
throw std::logic_error("unreachable: inactive constructor field at this instantiation");
}
}()};
} else {
if (std::holds_alternative<typename Dval<_U0, _U1,
_U2>::DIptr>(_other.v())) {
const auto& [i] = std::get<typename Dval<_U0, _U1,
_U2>::DIptr>(_other.v());
return DIptr{[&]() -> iptr {
if constexpr (crane_convertible<iptr, const _U1&>) {
return crane_convert<iptr>(i);
} else {
throw std::logic_error("unreachable: inactive constructor field at this instantiation");
}
}()};
} else {
const auto& [a] = std::get<typename Dval<_U0, _U1,
_U2>::DAddr>(_other.v());
return DAddr{[&]() -> ADDR {
if constexpr (crane_convertible<ADDR, const _U2&>) {
return crane_convert<ADDR>(a);
} else {
throw std::logic_error("unreachable: inactive constructor field at this instantiation");
}
}()};
}
}
}()) {}
static Dval<ptr, iptr, ADDR> dptr(ptr p) {
return Dval<ptr, iptr,
ADDR>(DPtr{std::move(p)});}
static Dval<ptr, iptr, ADDR> diptr(iptr i) {
return Dval<ptr, iptr,
ADDR>(DIptr{std::move(i)});}
static Dval<ptr, iptr, ADDR> daddr(ADDR a) {
return Dval<ptr, iptr,
ADDR>(DAddr{std::move(a)});}
  // MANIPULATORS
inline variant_t& v_mut() {
return v_;}
  // ACCESSORS
const variant_t& v() const {
return v_;}
};
struct natIPtr {
using iptr = Nat;
static Nat zero_iptr() {
return Nat::o();}
static EOU<Nat> from_Z(Nat n) {
return EOU_monad::template ret<Nat>(std::move(n));}
static Nat to_Z(Nat n) {
return n;}
};
static_assert(IPtr<natIPtr>);
struct ProvenanceV {
using prov = bool;
constexpr static bool nil_prov() {
return false;}
};
static_assert(Provenance<ProvenanceV>);
struct PointerV {
using ptr = std::pair<Nat, bool>;
static std::pair<Nat, bool> null() {
return std::make_pair(Nat::o(), false);}
};
static_assert(Pointer<PointerV>);template <IPtr
_tcI0>struct ParamsV {
using PROV = ProvenanceV;
using PTR = PointerV;
using IPTR = _tcI0;
using iptr = typename _tcI0::iptr;
using ADDR = Nat;
using prov = typename PROV::prov;
using ptr = typename PTR::ptr;
static Nat zero_addr() {
return Nat::o();}
};
struct NestedInstanceFieldResolution {
static inline const Dval<typename PointerV::ptr, typename ParamsV<natIPtr>::IPTR::iptr, typename ParamsV<natIPtr>::ADDR> boxed_ptr = Dval<typename PointerV::ptr, typename ParamsV<natIPtr>::IPTR::iptr, typename ParamsV<natIPtr>::ADDR>::dptr(PointerV::null());
static inline const Dval<typename ParamsV<natIPtr>::PTR::ptr, typename natIPtr::iptr, typename ParamsV<natIPtr>::ADDR> boxed_iptr = Dval<typename ParamsV<natIPtr>::PTR::ptr, typename natIPtr::iptr, typename ParamsV<natIPtr>::ADDR>::diptr(natIPtr::zero_iptr());static inline const Nat addr0 = crane::any_cast<Nat>(ParamsV<natIPtr>::zero_addr());
static inline const Nat run = []() {
auto&& _sv = boxed_iptr;
if (std::holds_alternative<typename Dval<typename ParamsV<natIPtr>::PTR::ptr, typename natIPtr::iptr, typename ParamsV<natIPtr>::ADDR>::DPtr>(_sv.v())) {
const auto& [p0] = std::get<typename Dval<typename ParamsV<natIPtr>::PTR::ptr, typename natIPtr::iptr, typename ParamsV<natIPtr>::ADDR>::DPtr>(_sv.v());
return p0.first;
} else if (std::holds_alternative<typename Dval<typename ParamsV<natIPtr>::PTR::ptr, typename natIPtr::iptr, typename ParamsV<natIPtr>::ADDR>::DIptr>(_sv.v())) {
const auto& [i0] = std::get<typename Dval<typename ParamsV<natIPtr>::PTR::ptr, typename natIPtr::iptr, typename ParamsV<natIPtr>::ADDR>::DIptr>(_sv.v());
return natIPtr::to_Z(i0);
} else {
const auto& [a0] = std::get<typename Dval<typename ParamsV<natIPtr>::PTR::ptr, typename natIPtr::iptr, typename ParamsV<natIPtr>::ADDR>::DAddr>(_sv.v());
return a0;
}
}();
};

#endif // INCLUDED_NESTED_INSTANCE_FIELD_RESOLUTION
