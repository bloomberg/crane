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

namespace bool0 {
struct true0;
struct false0;
using bool0 = std::variant<true0, false0>;
struct true0 {
  static std::shared_ptr<bool0> make();
};
struct false0 {
  static std::shared_ptr<bool0> make();
};
}; // namespace bool0

namespace nat {
struct O;
struct S;
using nat = std::variant<O, S>;
struct O {
  static std::shared_ptr<nat> make();
};
struct S {
  std::shared_ptr<nat> _a0;
  static std::shared_ptr<nat> make(std::shared_ptr<nat> _a0);
};
}; // namespace nat

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
std::shared_ptr<list::list<T1>> app(const std::shared_ptr<list::list<T1>> l,
                                    const std::shared_ptr<list::list<T1>> m) {
  return std::visit(
      Overloaded{
          [&](const list::nil<T1> _args) -> std::shared_ptr<list::list<T1>> {
            return m;
          },
          [&](const list::cons<T1> _args) -> std::shared_ptr<list::list<T1>> {
            T1 a = _args._a0;
            std::shared_ptr<list::list<T1>> l1 = _args._a1;
            return list::cons<T1>::make(a, app<T1>(l1, m));
          }},
      *l);
}

std::shared_ptr<nat::nat> add(const std::shared_ptr<nat::nat> n,
                              const std::shared_ptr<nat::nat> m);

std::shared_ptr<nat::nat> max(const std::shared_ptr<nat::nat> n,
                              const std::shared_ptr<nat::nat> m);

namespace Tree {
namespace tree {
template <typename A> struct leaf;
template <typename A> struct node;
template <typename A> using tree = std::variant<leaf<A>, node<A>>;
template <typename A> struct leaf {
  static std::shared_ptr<tree<A>> make() {
    return std::make_shared<tree<A>>(leaf<A>{});
  }
};
template <typename A> struct node {
  std::shared_ptr<tree<A>> _a0;
  A _a1;
  std::shared_ptr<tree<A>> _a2;
  static std::shared_ptr<tree<A>> make(std::shared_ptr<tree<A>> _a0, A _a1,
                                       std::shared_ptr<tree<A>> _a2) {
    return std::make_shared<tree<A>>(node<A>{_a0, _a1, _a2});
  }
};
}; // namespace tree

template <typename T1, typename T2,
          MapsTo<T2, std::shared_ptr<tree::tree<T1>>, T2, T1,
                 std::shared_ptr<tree::tree<T1>>, T2>
              F1>
T2 tree_rect(const T2 f, F1 &&f0, const std::shared_ptr<tree::tree<T1>> t) {
  return std::visit(
      Overloaded{[&](const tree::leaf<T1> _args) -> T2 { return f; },
                 [&](const tree::node<T1> _args) -> T2 {
                   std::shared_ptr<tree::tree<T1>> t0 = _args._a0;
                   T1 y = _args._a1;
                   std::shared_ptr<tree::tree<T1>> t1 = _args._a2;
                   return f0(t0, tree_rect<T1, T2>(f, f0, t0), y, t1,
                             tree_rect<T1, T2>(f, f0, t1));
                 }},
      *t);
}

template <typename T1, typename T2,
          MapsTo<T2, std::shared_ptr<tree::tree<T1>>, T2, T1,
                 std::shared_ptr<tree::tree<T1>>, T2>
              F1>
T2 tree_rec(const T2 f, F1 &&f0, const std::shared_ptr<tree::tree<T1>> t) {
  return std::visit(
      Overloaded{[&](const tree::leaf<T1> _args) -> T2 { return f; },
                 [&](const tree::node<T1> _args) -> T2 {
                   std::shared_ptr<tree::tree<T1>> t0 = _args._a0;
                   T1 y = _args._a1;
                   std::shared_ptr<tree::tree<T1>> t1 = _args._a2;
                   return f0(t0, tree_rec<T1, T2>(f, f0, t0), y, t1,
                             tree_rec<T1, T2>(f, f0, t1));
                 }},
      *t);
}

template <typename T1>
std::shared_ptr<bool0::bool0> is_leaf(const std::shared_ptr<tree::tree<T1>> t) {
  return std::visit(
      Overloaded{
          [&](const tree::leaf<T1> _args) -> std::shared_ptr<bool0::bool0> {
            return bool0::true0::make();
          },
          [&](const tree::node<T1> _args) -> std::shared_ptr<bool0::bool0> {
            return bool0::false0::make();
          }},
      *t);
}

template <typename T1>
std::shared_ptr<nat::nat> size(const std::shared_ptr<tree::tree<T1>> t) {
  return std::visit(
      Overloaded{[&](const tree::leaf<T1> _args) -> std::shared_ptr<nat::nat> {
                   return nat::S::make(nat::O::make());
                 },
                 [&](const tree::node<T1> _args) -> std::shared_ptr<nat::nat> {
                   std::shared_ptr<tree::tree<T1>> l = _args._a0;
                   std::shared_ptr<tree::tree<T1>> r = _args._a2;
                   return add(add(nat::S::make(nat::O::make()), size<T1>(l)),
                              size<T1>(r));
                 }},
      *t);
}

template <typename T1>
std::shared_ptr<nat::nat> height(const std::shared_ptr<tree::tree<T1>> t) {
  return std::visit(
      Overloaded{[&](const tree::leaf<T1> _args) -> std::shared_ptr<nat::nat> {
                   return nat::S::make(nat::O::make());
                 },
                 [&](const tree::node<T1> _args) -> std::shared_ptr<nat::nat> {
                   std::shared_ptr<tree::tree<T1>> l = _args._a0;
                   std::shared_ptr<tree::tree<T1>> r = _args._a2;
                   return add(nat::S::make(nat::O::make()),
                              max(height<T1>(l), height<T1>(r)));
                 }},
      *t);
}

template <typename T1>
std::shared_ptr<list::list<T1>>
flatten(const std::shared_ptr<tree::tree<T1>> t) {
  return std::visit(
      Overloaded{
          [&](const tree::leaf<T1> _args) -> std::shared_ptr<list::list<T1>> {
            return list::nil<T1>::make();
          },
          [&](const tree::node<T1> _args) -> std::shared_ptr<list::list<T1>> {
            std::shared_ptr<tree::tree<T1>> l = _args._a0;
            T1 x = _args._a1;
            std::shared_ptr<tree::tree<T1>> r = _args._a2;
            return app<T1>(flatten<T1>(l),
                           list::cons<T1>::make(x, flatten<T1>(r)));
          }},
      *t);
}

template <typename T1, MapsTo<T1, T1, T1> F0>
std::shared_ptr<tree::tree<T1>>
merge(F0 &&combine, const std::shared_ptr<tree::tree<T1>> t1,
      const std::shared_ptr<tree::tree<T1>> t2) {
  return std::visit(
      Overloaded{
          [&](const tree::leaf<T1> _args) -> std::shared_ptr<tree::tree<T1>> {
            return std::visit(
                Overloaded{[&](const tree::leaf<T1> _args)
                               -> std::shared_ptr<tree::tree<T1>> {
                             return tree::leaf<T1>::make();
                           },
                           [&](const tree::node<T1> _args)
                               -> std::shared_ptr<tree::tree<T1>> {
                             T1 a = _args._a1;
                             return tree::node<T1>::make(
                                 tree::leaf<T1>::make(), a,
                                 tree::leaf<T1>::make());
                           }},
                *t2);
          },
          [&](const tree::node<T1> _args) -> std::shared_ptr<tree::tree<T1>> {
            std::shared_ptr<tree::tree<T1>> l1 = _args._a0;
            T1 a1 = _args._a1;
            std::shared_ptr<tree::tree<T1>> r1 = _args._a2;
            return std::visit(
                Overloaded{
                    [&](const tree::leaf<T1> _args)
                        -> std::shared_ptr<tree::tree<T1>> {
                      return tree::node<T1>::make(tree::leaf<T1>::make(), a1,
                                                  tree::leaf<T1>::make());
                    },
                    [&](const tree::node<T1> _args)
                        -> std::shared_ptr<tree::tree<T1>> {
                      std::shared_ptr<tree::tree<T1>> l2 = _args._a0;
                      T1 a2 = _args._a1;
                      std::shared_ptr<tree::tree<T1>> r2 = _args._a2;
                      return tree::node<T1>::make(merge<T1>(combine, l1, l2),
                                                  combine(a1, a2),
                                                  merge<T1>(combine, r1, r2));
                    }},
                *t2);
          }},
      *t1);
}

const std::shared_ptr<tree::tree<std::shared_ptr<nat::nat>>> tree1 =
    tree::node<std::shared_ptr<nat::nat>>::make(
        tree::node<std::shared_ptr<nat::nat>>::make(
            tree::leaf<std::shared_ptr<nat::nat>>::make(),
            nat::S::make(nat::S::make(nat::S::make(nat::O::make()))),
            tree::node<std::shared_ptr<nat::nat>>::make(
                tree::leaf<std::shared_ptr<nat::nat>>::make(),
                nat::S::make(
                    nat::S::make(nat::S::make(nat::S::make(nat::S::make(
                        nat::S::make(nat::S::make(nat::O::make()))))))),
                tree::leaf<std::shared_ptr<nat::nat>>::make())),
        nat::S::make(nat::O::make()),
        tree::node<std::shared_ptr<nat::nat>>::make(
            tree::leaf<std::shared_ptr<nat::nat>>::make(),
            nat::S::make(
                nat::S::make(nat::S::make(nat::S::make(nat::O::make())))),
            tree::node<std::shared_ptr<nat::nat>>::make(
                tree::node<std::shared_ptr<nat::nat>>::make(
                    tree::leaf<std::shared_ptr<nat::nat>>::make(),
                    nat::S::make(nat::S::make(nat::S::make(nat::S::make(
                        nat::S::make(nat::S::make(nat::O::make())))))),
                    tree::leaf<std::shared_ptr<nat::nat>>::make()),
                nat::S::make(nat::S::make(nat::O::make())),
                tree::leaf<std::shared_ptr<nat::nat>>::make())));

}; // namespace Tree
