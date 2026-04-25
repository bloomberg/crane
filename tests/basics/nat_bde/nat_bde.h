#ifndef INCLUDED_NAT_BDE
#define INCLUDED_NAT_BDE

#include <bdlf_overloaded.h>
#include <bsl_concepts.h>
#include <bsl_functional.h>
#include <bsl_iostream.h>
#include <bsl_memory.h>
#include <bsl_stdexcept.h>
#include <bsl_string.h>
#include <bsl_type_traits.h>
#include <bsl_variant.h>


using namespace BloombergLP;
template <class From, class To>
concept convertible_to = bsl::is_convertible<From, To>::value;

template <class T, class U>
concept same_as = bsl::is_same<T, U>::value && bsl::is_same<U, T>::value;

template <class F, class R, class... Args>
concept MapsTo =
 requires (F& f, Args&... a) {
 { bsl::invoke(static_cast<F&>(f), static_cast<Args&>(a)...) }
 -> convertible_to<R>;
 };

struct Nat {
  // TYPES
struct O {

};
struct S {
bsl::unique_ptr<Nat> d_n;
};
using variant_t = bsl::variant<O,
S>;
private:
  // DATA
variant_t d_v_;
public:
  // CREATORS
Nat() {}
explicit Nat(O _v) : d_v_(_v) {}
explicit Nat(S _v) : d_v_(bsl::move(_v)) {}
Nat(const Nat& _other) : d_v_(bsl::move(_other.clone().d_v_)) {}
Nat(Nat&& _other) : d_v_(bsl::move(_other.d_v_)) {}
__attribute__((pure)) Nat& operator=(const Nat& _other) {
d_v_ = std::move(_other.clone().d_v_);
return *this;}
__attribute__((pure)) Nat& operator=(Nat&& _other) {
d_v_ = std::move(_other.d_v_);
return *this;}
  // ACCESSORS
__attribute__((pure)) Nat clone() const {
auto&& _sv = *(this);
if (bsl::holds_alternative<O>(_sv.v())) {
return Nat(O{});
} else {
const auto& [d_n] = bsl::get<S>(_sv.v());
return Nat(S{clone_as_value<std::unique_ptr<Nat>>(d_n)});
}}
  // CREATORS
__attribute__((pure)) static Nat o(){
return Nat(O{});}
__attribute__((pure)) static Nat s(const Nat& n){
return Nat(S{bsl::make_unique<Nat>(n.clone())});}
  // MANIPULATORS
__attribute__((pure)) variant_t& v_mut() {
return d_v_;}
  // ACCESSORS
__attribute__((pure)) Nat* operator->() {
return this;}
__attribute__((pure)) const Nat* operator->() const {
return this;}
__attribute__((pure)) bool operator!=(std::nullptr_t) const {
return true;}
__attribute__((pure)) bool operator==(std::nullptr_t) const {
return false;}
  // MANIPULATORS
void reset() {
*this = Nat();}
  // ACCESSORS
__attribute__((pure)) const variant_t& v() const {
return d_v_;}
template <typename T1, MapsTo<T1, Nat, T1> F1>
T1 nat_rect(const T1 f,
F1&& f0) const {
auto&& _sv = *(this);
if (bsl::holds_alternative<typename Nat::O>(_sv.v())) {
return f;
} else {
const auto& [d_n] = bsl::get<typename Nat::S>(_sv.v());
return f0(*(d_n), (*(d_n)).template nat_rect<T1>(f, f0));
}}
template <typename T1, MapsTo<T1, Nat, T1> F1>
T1 nat_rec(const T1 f,
F1&& f0) const {
auto&& _sv = *(this);
if (bsl::holds_alternative<typename Nat::O>(_sv.v())) {
return f;
} else {
const auto& [d_n] = bsl::get<typename Nat::S>(_sv.v());
return f0(*(d_n), (*(d_n)).template nat_rec<T1>(f,
f0));
}}
__attribute__((pure)) Nat add(Nat n) const {
auto&& _sv = *(this);
if (bsl::holds_alternative<typename Nat::O>(_sv.v())) {
return n;
} else {
const auto& [d_n] = bsl::get<typename Nat::S>(_sv.v());
return Nat::s((*(d_n)).add(n));
}}
__attribute__((pure)) int nat_to_int() const {
auto&& _sv = *(this);
if (bsl::holds_alternative<typename Nat::O>(_sv.v())) {
return 0;
} else {
const auto& [d_n] = bsl::get<typename Nat::S>(_sv.v());
return 1 + (*(d_n)).nat_to_int();
}}
};

#endif // INCLUDED_NAT_BDE
