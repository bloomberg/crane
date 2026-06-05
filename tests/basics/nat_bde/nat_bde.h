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
#include <bsl_vector.h>
#include <utility>

using namespace BloombergLP;
template <class From, class To>
concept convertible_to = bsl::is_convertible<From, To>::value;

template <class T, class U>
concept same_as = bsl::is_same<T, U>::value && bsl::is_same<U, T>::value;

struct Nat {
  // TYPES
  struct O {};
  struct S {
    bsl::shared_ptr<Nat> d_n;
  };
  using variant_t = bsl::variant<O, S>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  Nat() {}
  explicit Nat(O _v) : d_v_(_v) {}
  explicit Nat(S _v) : d_v_(bsl::move(_v)) {}
  static Nat o() { return Nat(O{}); }
  static Nat s(Nat n) { return Nat(S{bsl::make_shared<Nat>(bsl::move(n))}); }
  // MANIPULATORS
  ~Nat() {
    bsl::vector<bsl::shared_ptr<Nat>> _stack = {};
    auto _drain = [&](variant_t &_v) {
      if (auto *_alt = bsl::get_if<S>(&_v)) {
        if (_alt->d_n) {
          _stack.push_back(bsl::move(_alt->d_n));
        }
      }
    };
    _drain(v_mut());
    while (!_stack.empty()) {
      auto _cur = bsl::move(_stack.back());
      _stack.pop_back();
      if (_cur.use_count() == 1) {
        _drain(_cur->v_mut());
      }
    }
  }
  inline variant_t &v_mut() { return d_v_; }
  // ACCESSORS
  const variant_t &v() const { return d_v_; }
  template <typename T1, typename F1>
    requires bsl::is_invocable_r_v<T1, F1 &, Nat &, T1 &>
  T1 nat_rect(T1 f, F1 &&f0) const {
    if (bsl::holds_alternative<typename Nat::O>(this->v())) {
      return f;
    } else {
      const auto &[d_n] = bsl::get<typename Nat::S>(this->v());
      return f0(*d_n, d_n->template nat_rect<T1>(f, f0));
    }
  }
  template <typename T1, typename F1>
    requires bsl::is_invocable_r_v<T1, F1 &, Nat &, T1 &>
  T1 nat_rec(T1 f, F1 &&f0) const {
    if (bsl::holds_alternative<typename Nat::O>(this->v())) {
      return f;
    } else {
      const auto &[d_n] = bsl::get<typename Nat::S>(this->v());
      return f0(*d_n, d_n->template nat_rec<T1>(f, f0));
    }
  }
  Nat add(Nat n) const {
    if (bsl::holds_alternative<typename Nat::O>(this->v())) {
      return n;
    } else {
      const auto &[d_n] = bsl::get<typename Nat::S>(this->v());
      return Nat::s(d_n->add(bsl::move(n)));
    }
  }
  int nat_to_int() const {
    if (bsl::holds_alternative<typename Nat::O>(this->v())) {
      return 0;
    } else {
      const auto &[d_n] = bsl::get<typename Nat::S>(this->v());
      return 1 + d_n->nat_to_int();
    }
  }
};

#endif // INCLUDED_NAT_BDE
