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
      std::shared_ptr<List::list<A>> _a1;
    };
    using variant_t = std::variant<nil, cons>;

  private:
    variant_t v_;
    explicit list(nil x) : v_(std::move(x)) {}
    explicit list(cons x) : v_(std::move(x)) {}

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
    };
    const variant_t &v() const { return v_; }
  };
};

template <typename T1>
std::shared_ptr<List::list<T1>>
better_rev(const std::shared_ptr<List::list<T1>> &l) {
  std::function<std::shared_ptr<List::list<meta8>>(
      std::shared_ptr<List::list<meta8>>, std::shared_ptr<List::list<meta8>>)>
      go;
  go = [&](std::shared_ptr<List::list<meta8>> l0,
           std::shared_ptr<List::list<meta8>> acc)
      -> std::shared_ptr<List::list<meta8>> {
    return std::visit(
        Overloaded{[&](const typename List::list<meta8>::nil _args)
                       -> std::shared_ptr<List::list<meta8>> { return acc; },
                   [&](const typename List::list<meta8>::cons _args)
                       -> std::shared_ptr<List::list<meta8>> {
                     meta8 x = _args._a0;
                     std::shared_ptr<List::list<meta8>> xs = _args._a1;
                     return go(xs, List::list<meta8>::ctor::cons_(x, acc));
                   }},
        l0->v());
  };
  return go(l, List::list<T1>::ctor::nil_());
}
