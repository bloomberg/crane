#ifndef INCLUDED_INDUCTIVE_FIELD_AT_SECTION_CLASS_FIELD
#define INCLUDED_INDUCTIVE_FIELD_AT_SECTION_CLASS_FIELD

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
template <typename
A> struct EOU;
struct EOU_monad;
struct ProvenanceV;
struct Dval;
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
const auto& [a01] = std::get<typename EOU<_A0>::Ok>(m.v());
return k(a01);
} else {
const auto& [a01] = std::get<typename EOU<_A0>::Err>(m.v());
return EOU<_A1>::err(a01);
}}
};
static_assert(Monad<EOU_monad>);template <typename
I>concept IPtr = requires {
  typename I::iptr;
  { I::from_Z(std::declval<Nat>()) } -> std::convertible_to<EOU<typename I::iptr>>;
  { I::to_Z(std::declval<typename I::iptr>()) } -> std::convertible_to<Nat>;
} && (requires {
  { I::zero_iptr() } -> std::convertible_to<typename I::iptr>;
} || requires {
  { I::zero_iptr } -> std::convertible_to<typename I::iptr>;
});using iptr = std::any;template <typename
I>concept Provenance = requires {
  typename I::prov;
} && (requires {
  { I::nil_prov() } -> std::convertible_to<typename I::prov>;
} || requires {
  { I::nil_prov } -> std::convertible_to<typename I::prov>;
});using prov = std::any;template <typename
I>concept Pointer = requires {
  typename I::ptr;
} && (requires {
  { I::null() } -> std::convertible_to<typename I::ptr>;
} || requires {
  { I::null } -> std::convertible_to<typename I::ptr>;
});using ptr = std::any;template <typename
I>concept PI = requires {
  { I::ptr_to_int(std::declval<ptr>()) } -> std::convertible_to<Nat>;
  { I::int_to_ptr(std::declval<Nat>(),
std::declval<prov>()) } -> std::convertible_to<EOU<ptr>>;
};
struct ProvenanceV {
using prov = bool;
constexpr static bool nil_prov() {
return false;}
};
static_assert(Provenance<ProvenanceV>);template <IPtr
_tcI0>struct PointerV {
using iptr = typename _tcI0::iptr;
using ptr = std::pair<typename _tcI0::iptr, bool>;
static std::pair<typename _tcI0::iptr, bool> null() {
return std::make_pair(_tcI0::zero_iptr(), ProvenanceV::nil_prov());}
};template <IPtr
_tcI0>struct PIV {
using iptr = typename _tcI0::iptr;
static Nat ptr_to_int(typename PointerV<_tcI0>::ptr p) {
return _tcI0::to_Z(p.first);}
static EOU<typename PointerV<_tcI0>::ptr> int_to_ptr(Nat i,
typename ProvenanceV::prov pr) {
return EOU_monad::template bind<typename _tcI0::iptr,
std::pair<typename _tcI0::iptr, bool>>(_tcI0::from_Z(std::move(i)),
[=](typename _tcI0::iptr
a) mutable {
return EOU_monad::template ret<std::pair<typename _tcI0::iptr, bool>>(std::make_pair(a, pr));
});}
};
struct Dval {
  // TYPES
struct DPtr {
ptr p;
};
struct DNat {
Nat n;
};
using variant_t = std::variant<DPtr,
DNat>;
private:
  // DATA
variant_t v_;
public:
  // CREATORS
Dval() {}
explicit Dval(DPtr _v) : v_(std::move(_v)) {}
explicit Dval(DNat _v) : v_(std::move(_v)) {}
static Dval dptr(ptr p) {
return Dval(DPtr{std::move(p)});}
static Dval dnat(Nat n) {
return Dval(DNat{std::move(n)});}
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
struct InductiveFieldAtSectionClassField {
static inline const std::pair<Nat, bool> the_null = crane_any_cast<std::pair<Nat, bool>>(PointerV<natIPtr>::null());
static inline const Dval boxed = Dval::dptr(the_null);
static inline const Nat run = []() {
auto&& _sv2 = boxed;
if (std::holds_alternative<typename Dval::DPtr>(_sv2.v())) {
const auto& [p2] = std::get<typename Dval::DPtr>(_sv2.v());
return PIV<natIPtr>::ptr_to_int(p2);
} else {
const auto& [n2] = std::get<typename Dval::DNat>(_sv2.v());
return n2;
}
}();
};

#endif // INCLUDED_INDUCTIVE_FIELD_AT_SECTION_CLASS_FIELD
