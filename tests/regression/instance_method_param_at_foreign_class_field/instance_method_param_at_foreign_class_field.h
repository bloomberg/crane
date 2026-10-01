#ifndef INCLUDED_INSTANCE_METHOD_PARAM_AT_FOREIGN_CLASS_FIELD
#define INCLUDED_INSTANCE_METHOD_PARAM_AT_FOREIGN_CLASS_FIELD

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
struct natIPtr;using iptr = crane::obj;
using prov = crane::obj;template <typename
I>concept Monad = requires {
  typename I::template m<crane::obj>;
  { I::template ret<crane::obj>(std::declval<crane::obj>()) } -> std::convertible_to<typename I::template m<crane::obj>>;
  { I::template bind<crane::obj,
crane::obj>(std::declval<typename I::template m<crane::obj>>(),
std::declval<crane::fn<typename I::template m<crane::obj>(crane::obj)>>()) } -> std::convertible_to<typename I::template m<crane::obj>>;
};template <typename
I>concept IPtr = requires {
  typename I::iptr;
  typename I::prov;
  { I::from_Z(std::declval<Nat>()) } -> std::convertible_to<EOU<typename I::iptr>>;
  { I::prov_nat(std::declval<typename I::prov>()) } -> std::convertible_to<Nat>;
};
/// int_to_ptr returns EOU nat, not EOU ptr.  The carrier field is kept
/// -- the instance still builds it from iptr and prov -- but the method's
/// result stays concrete, so that a definition typed by a class field
/// projected through a known instance, which is a separate defect, is not on
/// this reduction's path.  See
/// instance_carrier_unqualified_at_known_instance.
template <typename I, typename
prov>concept ITOP = requires {
  typename I::ptr;
  { I::int_to_ptr(std::declval<Nat>(),
std::declval<prov>()) } -> std::convertible_to<EOU<Nat>>;
};
struct Nat {
  // TYPES
struct O {

};
struct S {
std::shared_ptr<Nat> a0;
};
using variant_t = std::variant<O,
S>;
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
auto _next = [&](variant_t&
_v) -> std::shared_ptr<Nat> {
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
using variant_t = std::variant<Ok,
Err>;
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
};struct EOU_monad {
template <typename _A0> using m = EOU<_A0>;
template <typename
_A0>
static EOU<_A0> ret(_A0 a) {
return EOU<_A0>::ok(std::move(a));}
template <typename _A0, typename _A1>
static EOU<_A1> bind(EOU<_A0> m,
crane::fn<EOU<_A1>(_A0)> k) {
if (std::holds_alternative<typename EOU<_A0>::Ok>(m.v())) {
const auto& [a01] = std::get<typename EOU<_A0>::Ok>(m.v());
return k(a01);
} else {
const auto& [a01] = std::get<typename EOU<_A0>::Err>(m.v());
return EOU<_A1>::err(a01);
}}
};
static_assert(Monad<EOU_monad>);template <IPtr
_tcI0>struct PIV {
using iptr = typename _tcI0::iptr;
using prov = typename _tcI0::prov;
using ptr = std::pair<typename _tcI0::iptr, typename _tcI0::prov>;
static EOU<Nat> int_to_ptr(Nat i,
typename _tcI0::prov pr) {
return EOU_monad::template bind<typename _tcI0::iptr,
Nat>(_tcI0::from_Z(std::move(i)),
[=](typename _tcI0::iptr) {
return EOU_monad::template ret<Nat>(_tcI0::prov_nat(pr));
});}
};
struct natIPtr {
using iptr = Nat;
using prov = bool;
static EOU<Nat> from_Z(Nat n) {
return EOU_monad::template ret<Nat>(std::move(n));}
static Nat prov_nat(bool b) {
if (b) { return Nat::s(Nat::o()); } else { return Nat::o(); }}
};
static_assert(IPtr<natIPtr>);
/// The match is the smallest consumer that still forces int_to_ptr to be
/// emitted.
struct InstanceMethodParamAtForeignClassField {
static inline const bool run = (std::holds_alternative<typename EOU<Nat>::Ok>(PIV<natIPtr>::int_to_ptr(Nat::s(Nat::o()),
true).v()) ? true : false);
};

#endif // INCLUDED_INSTANCE_METHOD_PARAM_AT_FOREIGN_CLASS_FIELD
