#ifndef INCLUDED_NAT_BDE
#define INCLUDED_NAT_BDE

#include <atomic>
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
    auto _next = [&](variant_t &_v) -> bsl::shared_ptr<Nat> {
      if (auto *_alt = bsl::get_if<S>(&_v)) {
        if (_alt->d_n && _alt->d_n.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          return bsl::move(_alt->d_n);
        }
      }
      return nullptr;
    };
    bsl::shared_ptr<Nat> _cur = _next(v_mut());
    while (_cur) {
      _cur = _next(_cur->v_mut());
    }
  }
  Nat(const Nat &) = default;
  Nat &operator=(const Nat &) = default;
  Nat(Nat &&) = default;
  Nat &operator=(Nat &&) = default;
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
      return f0(*d_n, d_n->template nat_rect<T1>(bsl::move(f), f0));
    }
  }
  template <typename T1, typename F1>
    requires bsl::is_invocable_r_v<T1, F1 &, Nat &, T1 &>
  T1 nat_rec(T1 f, F1 &&f0) const {
    if (bsl::holds_alternative<typename Nat::O>(this->v())) {
      return f;
    } else {
      const auto &[d_n] = bsl::get<typename Nat::S>(this->v());
      return f0(*d_n, d_n->template nat_rec<T1>(bsl::move(f), f0));
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
