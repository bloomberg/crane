#ifndef INCLUDED_CLASS_FIELD_ALIAS_AT_CALL_ARGUMENT
#define INCLUDED_CLASS_FIELD_ALIAS_AT_CALL_ARGUMENT

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
template <typename
A>struct EOU;
struct EOU_monad;
struct ProvenanceV;
struct natIPtr;using iptr = crane::obj;
using prov = crane::obj;
using ptr = crane::obj;template <typename
I>concept Monad = requires {
    typename I::template m<crane::obj>;
    { I::template ret<crane::obj>(std::declval<crane::obj>()) } -> std::convertible_to<typename I::template m<crane::obj>>;
    { I::template bind<crane::obj, crane::obj>(std::declval<typename I::template m<crane::obj>>(), std::declval<crane::fn<typename I::template m<crane::obj>(crane::obj)>>()) } -> std::convertible_to<typename I::template m<crane::obj>>;
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
  });template <typename I, typename ptr, typename
prov>concept PI = requires {
       { I::ptr_to_int(std::declval<ptr>()) } -> std::convertible_to<Nat>;
       { I::int_to_ptr(std::declval<Nat>(), std::declval<prov>()) } -> std::convertible_to<EOU<ptr>>;
     };
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
Nat(Nat&&) = default;
Nat& operator=(Nat&&) = default;
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
CraneU>
EOU(const EOU<CraneU>& _other) : v_([&]() -> variant_t {
if (std::holds_alternative<typename EOU<CraneU>::Ok>(_other.v())) {
const auto& [a0] = std::get<typename EOU<CraneU>::Ok>(_other.v());
return Ok{[&]() -> A {
if constexpr (crane_convertible<A, const CraneU&>) {
return crane_convert<A>(a0);
} else {
throw std::logic_error("unreachable: inactive constructor field at this instantiation");
}
}()};
} else {
const auto& [a0] = std::get<typename EOU<CraneU>::Err>(_other.v());
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
template <typename CraneA0> using m = EOU<CraneA0>;
template <typename
CraneA0>
static EOU<CraneA0> ret(CraneA0 a) {
return EOU<CraneA0>::ok(std::move(a));}
template <typename CraneA0, typename
CraneA1>
static EOU<CraneA1> bind(EOU<CraneA0> m, crane::fn<EOU<CraneA1>(CraneA0)> k) {
if (std::holds_alternative<typename EOU<CraneA0>::Ok>(m.v())) {
const auto& [a0] = std::get<typename EOU<CraneA0>::Ok>(m.v());
return k(a0);
} else {
const auto& [a0] = std::get<typename EOU<CraneA0>::Err>(m.v());
return EOU<CraneA1>::err(a0);
}}
};
static_assert(Monad<EOU_monad>);
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
return _tcI0::to_Z(std::move(p).first);}
static EOU<typename PointerV<_tcI0>::ptr> int_to_ptr(Nat i, typename ProvenanceV::prov pr) {
return EOU_monad::template bind<typename _tcI0::iptr,
std::pair<typename _tcI0::iptr, bool>>(_tcI0::from_Z(std::move(i)),
[=](const typename _tcI0::iptr&
a) {
return EOU_monad::template ret<std::pair<typename _tcI0::iptr, bool>>(std::make_pair(a, pr));
});}
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
struct ClassFieldAliasAtCallArgument {
static inline const std::pair<Nat, bool> the_null = crane_any_cast<std::pair<Nat, bool>>(PointerV<natIPtr>::null());
static Nat use(const typename PointerV<natIPtr>::ptr& p);
static inline const Nat run = use(the_null);
};

#endif // INCLUDED_CLASS_FIELD_ALIAS_AT_CALL_ARGUMENT
