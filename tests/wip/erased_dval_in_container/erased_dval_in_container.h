#ifndef INCLUDED_ERASED_DVAL_IN_CONTAINER
#define INCLUDED_ERASED_DVAL_IN_CONTAINER

#include <any>
#include <concepts>
#include <memory>
#include <stdexcept>
#include <utility>
#include <variant>
#include <optional>
#include <utility>
#include <memory>
#include "crane_fn.h"
#include "small_vector.h"
#include <atomic>





struct Nat;
template <typename A> struct List;
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
Nat add(Nat m) const {
std::shared_ptr<Nat> _head{};
std::shared_ptr<Nat>* _write = &_head;
const Nat* _loop_self = this;
Nat _loop_m = std::move(m);
while (true) {
auto&& _sv = *_loop_self;
if (std::holds_alternative<typename Nat::O>(_sv.v())) {
*_write = std::make_shared<Nat>(std::move(_loop_m));
break;
} else {
const auto& [a0] = std::get<typename Nat::S>(_sv.v());
auto _cell = std::make_shared<Nat>(typename Nat::S(nullptr));
*_write = std::move(_cell);
_write = &std::get<typename Nat::S>((*_write)->v_mut()).a0;
_loop_self = crane_raw(a0);
continue;
}
}
return std::move(*_head);}
};template <typename
A>struct List {
  // TYPES
struct Nil {

};
struct Cons {
A a;
std::shared_ptr<List<A>> l;
};
using variant_t = std::variant<Nil,
Cons>;
private:
  // DATA
variant_t v_;
public:
  // CREATORS
List() {}
explicit List(Nil _v) : v_(_v) {}
explicit List(Cons _v) : v_(std::move(_v)) {}
template <typename
_U>
List(const List<_U>& _other) {
if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
this->v_ = Nil{};
} else {
const auto& [a, l] = std::get<typename List<_U>::Cons>(_other.v());
this->v_ = Cons{[&]() -> A {
if constexpr (crane_convertible<A, const _U&>) {
return crane_convert<A>(a);
} else {
throw std::logic_error("unreachable: inactive constructor field at this instantiation");
}
}(),
(l ? std::make_shared<List<A>>(crane_convert<List<A>>(*l)) : nullptr)};
}}
static List<A> nil() {
return List<A>(Nil{});}
static List<A> cons(A a, List<A> l) {
return List<A>(Cons{std::move(a),
std::make_shared<List<A>>(std::move(l))});}
  // MANIPULATORS
~List() {
crane::small_vector<std::shared_ptr<List<A>>> _stack = {};
auto _drain = [&](variant_t&
_v) {
if (auto* _alt = std::get_if<Cons>(&_v)) {
if (_alt->l) {
_stack.push_back(std::move(_alt->l));
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
List(const List&) = default;
List& operator=(const List&) = default;
List(List&&) noexcept = default;
List& operator=(List&&) noexcept = default;
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
template <Params _tcI0>
std::optional<List<Dval<ptr,
iptr>>> wrap() const {
return std::make_optional<List<Dval<ptr, iptr>>>(List<Dval<ptr,
iptr>>::cons(std::move(*this), List<Dval<ptr, iptr>>::nil()));}
};template <Params _tcI0>List<Dval<typename _tcI0::PTR::ptr,
typename _tcI0::IPTR::iptr>> dlist(){return List<Dval<typename _tcI0::PTR::ptr,
typename _tcI0::IPTR::iptr>>::cons(Dval<typename _tcI0::PTR::ptr,
typename _tcI0::IPTR::iptr>::diptr(_tcI0::IPTR::zero_iptr()), List<Dval<typename _tcI0::PTR::ptr,
typename _tcI0::IPTR::iptr>>::nil());}template <Params
_tcI0>Nat sum_list(const List<Dval<typename _tcI0::PTR::ptr,
typename _tcI0::IPTR::iptr>>& l){if (std::holds_alternative<typename List<Dval<typename _tcI0::PTR::ptr,
typename _tcI0::IPTR::iptr>>::Nil>(l.v())) {
return Nat::o();
} else {
const auto& [a0, a1] = std::get<typename List<Dval<typename _tcI0::PTR::ptr,
typename _tcI0::IPTR::iptr>>::Cons>(l.v());
return [&]() {
if (std::holds_alternative<typename Dval<typename _tcI0::PTR::ptr,
typename _tcI0::IPTR::iptr>::DPtr>(a0.v())) {
return Nat::o();
} else {
const auto& [i0] = std::get<typename Dval<typename _tcI0::PTR::ptr,
typename _tcI0::IPTR::iptr>::DIptr>(a0.v());
return _tcI0::IPTR::to_Z(i0);
}
}().add(sum_list<_tcI0>(*a1));
}}
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
struct ErasedDvalInContainer {
static inline const List<Dval<typename ParamsV<natIPtr>::PTR::ptr,
typename ParamsV<natIPtr>::IPTR::iptr>> l0 = dlist<ParamsV<natIPtr>>();
static Nat s0(const List<Dval<typename ParamsV<natIPtr>::PTR::ptr,
typename ParamsV<natIPtr>::IPTR::iptr>>& x0_);
static std::optional<List<Dval<typename ParamsV<natIPtr>::PTR::ptr,
typename ParamsV<natIPtr>::IPTR::iptr>>> w0(const Dval<typename ParamsV<natIPtr>::PTR::ptr,
typename ParamsV<natIPtr>::IPTR::iptr>& x0_);
static inline const Nat run = s0(l0).add([]() -> Nat {
auto _cs = w0(Dval<typename ParamsV<natIPtr>::PTR::ptr,
typename natIPtr::iptr>::diptr(natIPtr::zero_iptr()));
if (_cs.has_value()) { const List<Dval<typename ParamsV<natIPtr>::PTR::ptr,
typename natIPtr::iptr>>& l = *_cs; return s0(l); } else { return Nat::o(); }
}());
};

#endif // INCLUDED_ERASED_DVAL_IN_CONTAINER
