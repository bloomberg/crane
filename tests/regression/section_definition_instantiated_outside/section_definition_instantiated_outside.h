#ifndef INCLUDED_SECTION_DEFINITION_INSTANTIATED_OUTSIDE
#define INCLUDED_SECTION_DEFINITION_INSTANTIATED_OUTSIDE

#include <any>
#include <concepts>
#include <memory>
#include <utility>
#include <variant>
#include <utility>
#include "small_vector.h"
#include <atomic>





struct Nat;
template <typename ptr, typename
iptr> struct Dval;
struct natIPtr;
struct ProvenanceV;
struct PointerV;
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
I>concept IPtr = requires {
  typename I::iptr;
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
});template <typename
I>concept Pointer = requires {
  typename I::ptr;
} && (requires {
  { I::null() } -> std::convertible_to<typename I::ptr>;
} || requires {
  { I::null } -> std::convertible_to<typename I::ptr>;
});using ptr = std::any;template <typename
I>concept Params = requires {
  typename I::ADDR;
  typename I::PROV;
  typename I::PTR;
  typename I::IPTR;
} && (requires {
  { I::zero_addr() } -> std::convertible_to<typename I::ADDR>;
} || requires {
  { I::zero_addr } -> std::convertible_to<typename I::ADDR>;
});template <typename ptr, typename
iptr>struct Dval {
  // TYPES
struct DPtr {
ptr p;
};
struct DIptr {
iptr i;
};
using variant_t = std::variant<DPtr,
DIptr>;
private:
  // DATA
variant_t v_;
public:
  // CREATORS
Dval() {}
explicit Dval(DPtr _v) : v_(std::move(_v)) {}
explicit Dval(DIptr _v) : v_(std::move(_v)) {}
template <typename _U0, typename _U1>
Dval(const Dval<_U0,
_U1>& _other) {
if (std::holds_alternative<typename Dval<_U0,
_U1>::DPtr>(_other.v())) {
const auto& [p] = std::get<typename Dval<_U0, _U1>::DPtr>(_other.v());
this->v_ = DPtr{p};
} else {
const auto& [i] = std::get<typename Dval<_U0, _U1>::DIptr>(_other.v());
this->v_ = DIptr{i};
}}
static Dval<ptr, iptr> dptr(ptr p) {
return Dval<ptr, iptr>(DPtr{std::move(p)});}
static Dval<ptr, iptr> diptr(iptr i) {
return Dval<ptr,
iptr>(DIptr{std::move(i)});}
  // MANIPULATORS
inline variant_t& v_mut() {
return v_;}
  // ACCESSORS
const variant_t& v() const {
return v_;}
template <Params
_tcI0>
Nat inner_eqb() const {
if (std::holds_alternative<typename Dval<ptr,
iptr>::DPtr>(this->v())) {
return Nat::o();
} else {
const auto& [i0] = std::get<typename Dval<ptr,
iptr>::DIptr>(this->v());
return _tcI0::IPTR::to_Z(i0);
}}
};template <Params _tcI0>Dval<typename _tcI0::PTR::ptr,
typename _tcI0::IPTR::iptr> inner_zero(){return Dval<typename _tcI0::PTR::ptr,
typename _tcI0::IPTR::iptr>::diptr(_tcI0::IPTR::zero_iptr());}
struct natIPtr {
using iptr = Nat;
static Nat zero_iptr() {
return Nat::o();}
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
struct SectionDefinitionInstantiatedOutside {
static Nat eqb0(const Dval<typename ParamsV<natIPtr>::PTR::ptr,
typename ParamsV<natIPtr>::IPTR::iptr>& x0_);
static inline const Dval<typename ParamsV<natIPtr>::PTR::ptr,
typename ParamsV<natIPtr>::IPTR::iptr> zero0 = inner_zero<ParamsV<natIPtr>>();
static inline const Nat run = eqb0(zero0);
};

#endif // INCLUDED_SECTION_DEFINITION_INSTANTIATED_OUTSIDE
