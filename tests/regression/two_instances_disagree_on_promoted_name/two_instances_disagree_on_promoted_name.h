#ifndef INCLUDED_TWO_INSTANCES_DISAGREE_ON_PROMOTED_NAME
#define INCLUDED_TWO_INSTANCES_DISAGREE_ON_PROMOTED_NAME

#include <any>
#include <concepts>
#include <memory>
#include <utility>
#include <variant>
#include "crane_fn.h"
#include "small_vector.h"
#include <atomic>





struct Nat;
template <typename iptr> struct Dval;
struct natIPtr;
struct boolIPtr;
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
const auto& [a1] = std::get<typename Nat::S>(_sv.v());
auto _cell = std::make_shared<Nat>(typename Nat::S(nullptr));
*_write = std::move(_cell);
_write = &std::get<typename Nat::S>((*_write)->v_mut()).a0;
_loop_self = crane_raw(a1);
continue;
}
}
return std::move(*_head);}
};template <typename
I>concept IPtr = requires {
  typename I::iptr;
  { I::to_Z(std::declval<typename I::iptr>()) } -> std::convertible_to<Nat>;
} && (requires {
  { I::zero_iptr() } -> std::convertible_to<typename I::iptr>;
} || requires {
  { I::zero_iptr } -> std::convertible_to<typename I::iptr>;
});using iptr = std::any;template <typename
iptr>struct Dval {
  // TYPES
struct DIptr {
iptr i;
};
struct DNat {
Nat n;
};
using variant_t = std::variant<DIptr,
DNat>;
private:
  // DATA
variant_t v_;
public:
  // CREATORS
Dval() {}
explicit Dval(DIptr _v) : v_(std::move(_v)) {}
explicit Dval(DNat _v) : v_(std::move(_v)) {}
template <typename
_U>
Dval(const Dval<_U>& _other) {
if (std::holds_alternative<typename Dval<_U>::DIptr>(_other.v())) {
const auto& [i] = std::get<typename Dval<_U>::DIptr>(_other.v());
this->v_ = DIptr{i};
} else {
const auto& [n] = std::get<typename Dval<_U>::DNat>(_other.v());
this->v_ = DNat{n};
}}
static Dval<iptr> diptr(iptr i) {
return Dval<iptr>(DIptr{std::move(i)});}
static Dval<iptr> dnat(Nat n) {
return Dval<iptr>(DNat{std::move(n)});}
  // MANIPULATORS
inline variant_t& v_mut() {
return v_;}
  // ACCESSORS
const variant_t& v() const {
return v_;}
template <IPtr
_tcI0>
Nat to_nat() const {
if (std::holds_alternative<typename Dval<iptr>::DIptr>(this->v())) {
const auto& [i0] = std::get<typename Dval<iptr>::DIptr>(this->v());
return _tcI0::to_Z(i0);
} else {
const auto& [n0] = std::get<typename Dval<iptr>::DNat>(this->v());
return n0;
}}
};template <IPtr
_tcI0>Dval<typename _tcI0::iptr> inner(){return Dval<typename _tcI0::iptr>::diptr(_tcI0::zero_iptr());}
struct natIPtr {
using iptr = Nat;
static Nat zero_iptr() {
return Nat::o();}
static Nat to_Z(Nat n) {
return n;}
};
static_assert(IPtr<natIPtr>);
struct boolIPtr {
using iptr = bool;
constexpr static bool zero_iptr() {
return false;}
static Nat to_Z(bool b) {
if (b) { return Nat::s(Nat::o()); } else { return Nat::o(); }}
};
static_assert(IPtr<boolIPtr>);
struct TwoInstancesDisagreeOnPromotedName {
static inline const Dval<typename natIPtr::iptr> a0 = inner<natIPtr>();
static inline const Dval<typename boolIPtr::iptr> b0 = inner<boolIPtr>();
static inline const Nat run = []() {
auto x = inner<natIPtr>();
auto y = inner<boolIPtr>();
return std::move(x).template to_nat<natIPtr>().add(std::move(y).template to_nat<boolIPtr>()).add(a0.template to_nat<natIPtr>()).add(b0.template to_nat<boolIPtr>());
}();
};

#endif // INCLUDED_TWO_INSTANCES_DISAGREE_ON_PROMOTED_NAME
