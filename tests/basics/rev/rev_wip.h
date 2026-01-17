#include <functional>
#include <iostream>
#include <memory>
#include <string>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

struct List {
  template <typename A> struct list {
  public:
    struct nil {};
    struct cons {
      A _a0;
      std::shared_ptr<list<A>> _a1;
    };
    using variant_t = std::variant<nil, cons>;

  private:
    variant_t v_;
    explicit list(nil x) : v_(std::move(x)) {}
    explicit list(cons x) : v_(std::move(x)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<list<A>> nil_() {
        return std::shared_ptr<list<A>>(new list<A>(nil{}));
      }
      static std::shared_ptr<list<A>> cons_(A a0, std::shared_ptr<list<A>> a1) {
        return std::shared_ptr<list<A>>(new list<A>(cons{a0, a1}));
      }
    };
    const variant_t &v() const { return v_; }
  };
};

template <typename T1>
std::shared_ptr<List::list<T1>>
better_rev(const std::shared_ptr<List::list<T1>> l) {
  auto go = [&](auto l0, auto acc) {
    return std::visit(
        Overloaded{[&](auto _args) -> auto { return acc; },
                   [&](auto _args) -> auto {
                     auto x = _args._a0;
                     auto xs = _args._a1;
                     return go(xs, List::list<auto>::ctor::cons_(x, acc));
                   }},
        l0->v());
  };
  return go(l, List::list<T1>::ctor::nil_());
}
