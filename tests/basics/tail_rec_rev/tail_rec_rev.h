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
};

template <typename T1>
std::shared_ptr<List<T1>> better_rev(const std::shared_ptr<List<T1>> &l) {
  std::function<std::shared_ptr<List<T1>>(std::shared_ptr<List<T1>>,
                                          std::shared_ptr<List<T1>>)>
      go;
  go = [&](std::shared_ptr<List<T1>> l0,
           std::shared_ptr<List<T1>> acc) -> std::shared_ptr<List<T1>> {
    return std::visit(
        Overloaded{[&](const typename List<T1>::nil _args)
                       -> std::shared_ptr<List<T1>> { return std::move(acc); },
                   [&](const typename List<T1>::cons _args)
                       -> std::shared_ptr<List<T1>> {
                     T1 x = _args._a0;
                     std::shared_ptr<List<T1>> xs = _args._a1;
                     return go(std::move(xs),
                               List<T1>::ctor::cons_(x, std::move(acc)));
                   }},
        l0->v());
  };
  return go(l, List<T1>::ctor::nil_());
}
