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

namespace list {
template <typename A> struct nil;
template <typename A> struct cons;
template <typename A> using list = std::variant<nil<A>, cons<A>>;
template <typename A> struct nil {
  static std::shared_ptr<list<A>> make() {
    return std::make_shared<list<A>>(nil<A>{});
  }
};
template <typename A> struct cons {
  A _a0;
  std::shared_ptr<list<A>> _a1;
  static std::shared_ptr<list<A>> make(A _a0, std::shared_ptr<list<A>> _a1) {
    return std::make_shared<list<A>>(cons<A>{_a0, _a1});
  }
};
}; // namespace list

template <typename T1>
std::shared_ptr<list::list<T1>>
better_rev(const std::shared_ptr<list::list<T1>> l) {
  std::function<std::shared_ptr<list::list<meta8>>(
      std::shared_ptr<list::list<meta8>>, std::shared_ptr<list::list<meta8>>)>
      go;
  go = [&](std::shared_ptr<list::list<meta8>> l0,
           std::shared_ptr<list::list<meta8>> acc)
      -> std::shared_ptr<list::list<meta8>> {
    return std::visit(
        Overloaded{[&](const list::nil<meta8> _args)
                       -> std::shared_ptr<list::list<meta8>> { return acc; },
                   [&](const list::cons<meta8> _args)
                       -> std::shared_ptr<list::list<meta8>> {
                     meta8 x = _args._a0;
                     std::shared_ptr<list::list<meta8>> xs = _args._a1;
                     return go(xs, list::cons<meta8>::make(x, acc));
                   }},
        *l0);
  };
  return go(l, list::nil<T1>::make());
}
