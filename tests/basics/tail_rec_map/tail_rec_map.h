#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

template <typename A> struct List {
public:
  struct nil {};
  struct cons {
    A _a0;
    std::shared_ptr<List<A>> _a1;
  };
  using variant_t = std::variant<nil, cons>;

private:
  variant_t v_;
  explicit List(nil _v) : v_(std::move(_v)) {}
  explicit List(cons _v) : v_(std::move(_v)) {}

public:
  struct ctor {
    ctor() = delete;
    static std::shared_ptr<List<A>> nil_() {
      return std::shared_ptr<List<A>>(new List<A>(nil{}));
    }
    static std::shared_ptr<List<A>> cons_(A a0,
                                          const std::shared_ptr<List<A>> &a1) {
      return std::shared_ptr<List<A>>(new List<A>(cons{a0, a1}));
    }
    static std::unique_ptr<List<A>> nil_uptr() {
      return std::unique_ptr<List<A>>(new List<A>(nil{}));
    }
    static std::unique_ptr<List<A>>
    cons_uptr(A a0, const std::shared_ptr<List<A>> &a1) {
      return std::unique_ptr<List<A>>(new List<A>(cons{a0, a1}));
    }
  };
  const variant_t &v() const { return v_; }
  variant_t &v_mut() { return v_; }
  std::shared_ptr<List<A>> rev() const {
    return std::visit(
        Overloaded{
            [](const typename List<A>::nil _args) -> std::shared_ptr<List<A>> {
              return List<A>::ctor::nil_();
            },
            [](const typename List<A>::cons _args) -> std::shared_ptr<List<A>> {
              A x = _args._a0;
              std::shared_ptr<List<A>> l_ = _args._a1;
              return std::move(l_)->rev()->app(
                  List<A>::ctor::cons_(x, List<A>::ctor::nil_()));
            }},
        this->v());
  }
  std::shared_ptr<List<A>> app(std::shared_ptr<List<A>> m) const {
    return std::visit(Overloaded{[&](const typename List<A>::nil _args)
                                     -> std::shared_ptr<List<A>> { return m; },
                                 [&](const typename List<A>::cons _args)
                                     -> std::shared_ptr<List<A>> {
                                   A a = _args._a0;
                                   std::shared_ptr<List<A>> l1 = _args._a1;
                                   return List<A>::ctor::cons_(
                                       a, std::move(l1)->app(m));
                                 }},
                      this->v());
  }
};

template <typename T1, typename T2, MapsTo<T2, T1> F0>
std::shared_ptr<List<T2>> better_map(F0 &&f,
                                     const std::shared_ptr<List<T1>> &l) {
  std::function<std::shared_ptr<List<T2>>(std::shared_ptr<List<T1>>,
                                          std::shared_ptr<List<T2>>)>
      go;
  go = [&](std::shared_ptr<List<T1>> l0,
           std::shared_ptr<List<T2>> acc) -> std::shared_ptr<List<T2>> {
    return std::visit(
        Overloaded{
            [&](const typename List<T1>::nil _args)
                -> std::shared_ptr<List<T2>> { return std::move(acc)->rev(); },
            [&](const typename List<T1>::cons _args)
                -> std::shared_ptr<List<T2>> {
              T1 x = _args._a0;
              std::shared_ptr<List<T1>> xs = _args._a1;
              return go(std::move(xs),
                        List<T2>::ctor::cons_(f(x), std::move(acc)));
            }},
        l0->v());
  };
  return go(l, List<T2>::ctor::nil_());
}
