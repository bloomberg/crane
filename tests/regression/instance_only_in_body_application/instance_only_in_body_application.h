#ifndef INCLUDED_INSTANCE_ONLY_IN_BODY_APPLICATION
#define INCLUDED_INSTANCE_ONLY_IN_BODY_APPLICATION

#include <any>
#include <atomic>
#include <concepts>
#include <memory>
#include <stdexcept>
#include <utility>
#include <variant>
#include <variant>
#include <utility>
#include "obj.h"
#include "crane_fn.h"





struct Nat;
template <typename A, typename B>struct Sum;
template <typename ptr, typename
iptr>struct Dval;
struct natIPtr;
struct ProvenanceV;
struct PointerV;using iptr = crane::obj;
using ptr = crane::obj;template <typename
I>concept IPtr = requires {
    typename I::iptr;
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
};template <typename A, typename
B>struct Sum {
  // TYPES
struct Inl {
A a0;
};
struct Inr {
B a0;
};
using variant_t = std::variant<Inl, Inr>;
private:
  // DATA
variant_t v_;
public:
  // CREATORS
Sum() {}
explicit Sum(Inl _v) : v_(std::move(_v)) {}
explicit Sum(Inr _v) : v_(std::move(_v)) {}
template <typename _U0, typename _U1>
Sum(const Sum<_U0,
_U1>& _other) : v_([&]() -> variant_t {
if (std::holds_alternative<typename Sum<_U0,
_U1>::Inl>(_other.v())) {
const auto& [a0] = std::get<typename Sum<_U0, _U1>::Inl>(_other.v());
return Inl{[&]() -> A {
if constexpr (crane_convertible<A, const _U0&>) {
return crane_convert<A>(a0);
} else {
throw std::logic_error("unreachable: inactive constructor field at this instantiation");
}
}()};
} else {
const auto& [a0] = std::get<typename Sum<_U0, _U1>::Inr>(_other.v());
return Inr{[&]() -> B {
if constexpr (crane_convertible<B, const _U1&>) {
return crane_convert<B>(a0);
} else {
throw std::logic_error("unreachable: inactive constructor field at this instantiation");
}
}()};
}
}()) {}
static Sum<A, B> inl(A a0) {
return Sum<A,
B>(Inl{std::move(a0)});}
static Sum<A, B> inr(B a0) {
return Sum<A,
B>(Inr{std::move(a0)});}
  // MANIPULATORS
inline variant_t& v_mut() {
return v_;}
  // ACCESSORS
const variant_t& v() const {
return v_;}
};template <typename ptr, typename
iptr>struct Dval {
  // TYPES
struct DPtr {
ptr p;
};
struct DIptr {
iptr i;
};
using variant_t = std::variant<DPtr, DIptr>;
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
_U1>& _other) : v_([&]() -> variant_t {
if (std::holds_alternative<typename Dval<_U0,
_U1>::DPtr>(_other.v())) {
const auto& [p] = std::get<typename Dval<_U0, _U1>::DPtr>(_other.v());
return DPtr{[&]() -> ptr {
if constexpr (crane_convertible<ptr, const _U0&>) {
return crane_convert<ptr>(p);
} else {
throw std::logic_error("unreachable: inactive constructor field at this instantiation");
}
}()};
} else {
const auto& [i] = std::get<typename Dval<_U0, _U1>::DIptr>(_other.v());
return DIptr{[&]() -> iptr {
if constexpr (crane_convertible<iptr, const _U1&>) {
return crane_convert<iptr>(i);
} else {
throw std::logic_error("unreachable: inactive constructor field at this instantiation");
}
}()};
}
}()) {}
static Dval<ptr, iptr> dptr(ptr p) {
return Dval<ptr,
iptr>(DPtr{std::move(p)});}
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
Nat to_nat() const {
if (std::holds_alternative<typename Dval<ptr,
iptr>::DPtr>(this->v())) {
return Nat::o();
} else {
const auto& [i0] = std::get<typename Dval<ptr,
iptr>::DIptr>(this->v());
return _tcI0::IPTR::to_Z(i0);
}}
};template <Params
_tcI0>Sum<Nat, Dval<typename _tcI0::PTR::ptr, typename _tcI0::IPTR::iptr>> runS(const Nat&){return Sum<Nat,
Dval<typename _tcI0::PTR::ptr,
typename _tcI0::IPTR::iptr>>::inr(Dval<typename _tcI0::PTR::ptr,
typename _tcI0::IPTR::iptr>::diptr(_tcI0::IPTR::zero_iptr()));}
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
};struct InstanceOnlyInBodyApplication {
static Nat check(std::monostate _x);
static inline const Nat run = check(std::monostate{});
};

#endif // INCLUDED_INSTANCE_ONLY_IN_BODY_APPLICATION
