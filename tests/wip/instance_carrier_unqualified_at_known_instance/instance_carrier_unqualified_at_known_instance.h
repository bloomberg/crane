#ifndef INCLUDED_INSTANCE_CARRIER_UNQUALIFIED_AT_KNOWN_INSTANCE
#define INCLUDED_INSTANCE_CARRIER_UNQUALIFIED_AT_KNOWN_INSTANCE

#include <any>
#include <concepts>
#include <functional>
#include <memory>
#include <stdexcept>
#include <utility>
#include <variant>
#include <crane_itree.h>
#include <utility>
#include "crane_fn.h"
#include "small_vector.h"
#include <atomic>





struct Nat;
template <typename A> struct EOU;
struct EOU_monad;
struct natIPtr;
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
crane::small_vector<std::shared_ptr<Nat>> _stack = {};
auto _drain = [&](variant_t&
_v) {
if (auto* _alt = std::get_if<S>(&_v)) {
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
I>concept Monad = requires {
  typename I::template m<std::any>;
  { I::template ret<std::any>(std::declval<std::any>()) } -> std::convertible_to<typename I::template m<std::any>>;
  { I::template bind<std::any,
std::any>(std::declval<typename I::template m<std::any>>(),
std::declval<std::function<typename I::template m<std::any>(std::any)>>()) } -> std::convertible_to<typename I::template m<std::any>>;
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
EOU(const EOU<_U>& _other) {
if (std::holds_alternative<typename EOU<_U>::Ok>(_other.v())) {
const auto& [a0] = std::get<typename EOU<_U>::Ok>(_other.v());
this->v_ = Ok{[&]() -> A {
if constexpr (crane_convertible<A, const _U&>) {
return crane_convert<A>(a0);
} else {
throw std::logic_error("unreachable: inactive constructor field at this instantiation");
}
}()};
} else {
const auto& [a0] = std::get<typename EOU<_U>::Err>(_other.v());
this->v_ = Err{a0};
}}
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
std::function<EOU<_A1>(_A0)> k) {
if (std::holds_alternative<typename EOU<_A0>::Ok>(m.v())) {
const auto& [a00] = std::get<typename EOU<_A0>::Ok>(m.v());
return k(a00);
} else {
const auto& [a00] = std::get<typename EOU<_A0>::Err>(m.v());
return EOU<_A1>::err(a00);
}}
};
static_assert(Monad<EOU_monad>);template <typename
I>concept IPtr = requires {
  typename I::iptr;
  typename I::prov;
  { I::from_Z(std::declval<Nat>()) } -> std::convertible_to<EOU<typename I::iptr>>;
};using iptr = std::any;using prov = std::any;template <typename
I>concept ITOP = requires {
  typename I::ptr;
  { I::int_to_ptr(std::declval<Nat>(),
std::declval<prov>()) } -> std::convertible_to<EOU<typename I::ptr>>;
};using ptr = std::any;template <IPtr
_tcI0>struct PIV {
using iptr = typename _tcI0::iptr;
using prov = typename _tcI0::prov;
using ptr = std::pair<typename _tcI0::iptr, typename _tcI0::prov>;
static EOU<std::pair<typename _tcI0::iptr, typename _tcI0::prov>> int_to_ptr(Nat i,
typename _tcI0::prov pr) {
return EOU_monad::template bind<typename _tcI0::iptr,
std::pair<typename _tcI0::iptr, typename _tcI0::prov>>(_tcI0::from_Z(std::move(i)),
[=](typename _tcI0::iptr
a) mutable {
return EOU_monad::template ret<std::pair<typename _tcI0::iptr, typename _tcI0::prov>>(std::make_pair(a, pr));
});}
};
struct natIPtr {
using iptr = Nat;
using prov = bool;
static EOU<Nat> from_Z(Nat n) {
return EOU_monad::template ret<Nat>(std::move(n));}
};
static_assert(IPtr<natIPtr>);
struct InstanceCarrierUnqualifiedAtKnownInstance {
static inline const EOU<ptr> run = PIV<natIPtr>::int_to_ptr(Nat::s(Nat::o()),
true);
};

#endif // INCLUDED_INSTANCE_CARRIER_UNQUALIFIED_AT_KNOWN_INSTANCE
