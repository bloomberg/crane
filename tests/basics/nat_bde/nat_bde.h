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
Nat& operator=(const Nat& _other) {
d_v_ = bsl::move(_other.clone().d_v_);
return *this;}
Nat& operator=(Nat&& _other) {
d_v_ = bsl::move(_other.d_v_);
return *this;}
  // ACCESSORS
Nat clone() const {
Nat _out{};
struct _CloneFrame { const Nat* _src; Nat* _dst; };
std::vector<_CloneFrame> _stack{};
_stack.push_back({this,
&_out});
while (!_stack.empty()) {
auto _frame = _stack.back();
_stack.pop_back();
const Nat* _src = _frame._src;
Nat* _dst = _frame._dst;
if (bsl::holds_alternative<O>(_src->v())) {
_dst->d_v_ = O{};
} else {
const auto& _alt = bsl::get<S>(_src->v());
_dst->d_v_ = S{_alt.d_n ? bsl::make_unique<Nat>() : nullptr};
auto& _dst_alt = std::get<S>(_dst->d_v_);
if (_alt.d_n) {
_stack.push_back({_alt.d_n.get(),
_dst_alt.d_n.get()});
}
}
}
return _out;}
  // CREATORS
static Nat o(){
return Nat(O{});}
static Nat s(Nat n){
return Nat(S{bsl::make_unique<Nat>(bsl::move(n))});}
  // MANIPULATORS
~Nat() {
std::vector<bsl::unique_ptr<Nat>> _stack{};
auto _drain = [&](Nat&
_node) {
if (std::holds_alternative<S>(_node.d_v_)) {
auto& _alt = std::get<S>(_node.d_v_);
if (_alt.d_n) {
_stack.push_back(bsl::move(_alt.d_n));
}
}
};
_drain(*this);
while (!_stack.empty()) {
auto _node = bsl::move(_stack.back());
_stack.pop_back();
if (_node) {
_drain(*_node);
}
}
}
inline variant_t& v_mut() {
return d_v_;}
  // ACCESSORS
const variant_t& v() const {
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
Nat add(Nat n) const {
auto&& _sv = *(this);
if (bsl::holds_alternative<typename Nat::O>(_sv.v())) {
return n;
} else {
const auto& [d_n] = bsl::get<typename Nat::S>(_sv.v());
return Nat::s((*(d_n)).add(bsl::move(n)));
}}
int nat_to_int() const {
auto&& _sv = *(this);
if (bsl::holds_alternative<typename Nat::O>(_sv.v())) {
return 0;
} else {
const auto& [d_n] = bsl::get<typename Nat::S>(_sv.v());
return 1 + (*(d_n)).nat_to_int();
}}
};

#endif // INCLUDED_NAT_BDE
