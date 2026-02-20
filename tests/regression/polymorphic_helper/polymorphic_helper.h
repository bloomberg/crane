#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

struct Nat {
  struct nat {
  public:
    struct O {};
    struct S {
      std::shared_ptr<Nat::nat> _a0;
    };
    using variant_t = std::variant<O, S>;

  private:
    variant_t v_;
    explicit nat(O _v) : v_(std::move(_v)) {}
    explicit nat(S _v) : v_(std::move(_v)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<Nat::nat> O_() {
        return std::shared_ptr<Nat::nat>(new Nat::nat(O{}));
      }
      static std::shared_ptr<Nat::nat> S_(const std::shared_ptr<Nat::nat> &a0) {
        return std::shared_ptr<Nat::nat>(new Nat::nat(S{a0}));
      }
      static std::unique_ptr<Nat::nat> O_uptr() {
        return std::unique_ptr<Nat::nat>(new Nat::nat(O{}));
      }
      static std::unique_ptr<Nat::nat>
      S_uptr(const std::shared_ptr<Nat::nat> &a0) {
        return std::unique_ptr<Nat::nat>(new Nat::nat(S{a0}));
      }
    };
    const variant_t &v() const { return v_; }
  };
};

struct List {
  template <typename A> struct list {
  public:
    struct nil {};
    struct cons {
      A _a0;
      std::shared_ptr<List::list<A>> _a1;
    };
    using variant_t = std::variant<nil, cons>;

  private:
    variant_t v_;
    explicit list(nil _v) : v_(std::move(_v)) {}
    explicit list(cons _v) : v_(std::move(_v)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<List::list<A>> nil_() {
        return std::shared_ptr<List::list<A>>(new List::list<A>(nil{}));
      }
      static std::shared_ptr<List::list<A>>
      cons_(A a0, const std::shared_ptr<List::list<A>> &a1) {
        return std::shared_ptr<List::list<A>>(new List::list<A>(cons{a0, a1}));
      }
      static std::unique_ptr<List::list<A>> nil_uptr() {
        return std::unique_ptr<List::list<A>>(new List::list<A>(nil{}));
      }
      static std::unique_ptr<List::list<A>>
      cons_uptr(A a0, const std::shared_ptr<List::list<A>> &a1) {
        return std::unique_ptr<List::list<A>>(new List::list<A>(cons{a0, a1}));
      }
    };
    const variant_t &v() const { return v_; }
    std::shared_ptr<Nat::nat> length() const {
      return std::visit(Overloaded{[](const typename List::list<A>::nil _args)
                                       -> std::shared_ptr<Nat::nat> {
                                     return Nat::nat::ctor::O_();
                                   },
                                   [](const typename List::list<A>::cons _args)
                                       -> std::shared_ptr<Nat::nat> {
                                     std::shared_ptr<List::list<A>> l_ =
                                         _args._a1;
                                     return Nat::nat::ctor::S_(l_->length());
                                   }},
                        this->v());
    }
  };
};

template <typename T1>
std::shared_ptr<Nat::nat> _foo_aux(const T1 a,
                                   const std::shared_ptr<Nat::nat> &n) {
  return repeat<T1>(a, n)->length();
}
std::shared_ptr<Nat::nat> add(const std::shared_ptr<Nat::nat> &n,
                              const std::shared_ptr<Nat::nat> &m);

template <typename T1>
std::shared_ptr<List::list<T1>> repeat(const T1 x,
                                       const std::shared_ptr<Nat::nat> &n) {
  return std::visit(Overloaded{[](const typename Nat::nat::O _args)
                                   -> std::shared_ptr<List::list<T1>> {
                                 return List::list<T1>::ctor::nil_();
                               },
                               [&](const typename Nat::nat::S _args)
                                   -> std::shared_ptr<List::list<T1>> {
                                 std::shared_ptr<Nat::nat> k = _args._a0;
                                 return List::list<T1>::ctor::cons_(
                                     x, repeat<T1>(x, k));
                               }},
                    n->v());
}

std::shared_ptr<Nat::nat> foo(const std::shared_ptr<Nat::nat> &n, const bool b);
