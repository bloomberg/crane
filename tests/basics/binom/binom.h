#include <algorithm>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <string>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

struct List {
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
};

struct Binom {
  using key = unsigned int;

  struct Tree {
    struct Node;
    struct Leaf;
    using tree = std::variant<Node, Leaf>;
    struct Node {
      key _a0;
      std::shared_ptr<tree> _a1;
      std::shared_ptr<tree> _a2;
      static std::shared_ptr<tree> make(key _a0, std::shared_ptr<tree> _a1,
                                        std::shared_ptr<tree> _a2);
    };
    struct Leaf {
      static std::shared_ptr<tree> make();
    };
  };

  template <typename T1,
            MapsTo<T1, unsigned int, std::shared_ptr<typename Tree::tree>, T1,
                   std::shared_ptr<typename Tree::tree>, T1>
                F0>
  T1 tree_rect(F0 &&f, const T1 f0,
               const std::shared_ptr<typename Tree::tree> t) {
    return std::visit(
        Overloaded{[&](const typename Tree::Node _args) -> T1 {
                     unsigned int k = _args._a0;
                     std::shared_ptr<typename Tree::tree> t0 = _args._a1;
                     std::shared_ptr<typename Tree::tree> t1 = _args._a2;
                     return f(k, t0, tree_rect<T1>(f, f0, t0), t1,
                              tree_rect<T1>(f, f0, t1));
                   },
                   [&](const typename Tree::Leaf _args) -> T1 { return f0; }},
        *t);
  }

  template <typename T1,
            MapsTo<T1, unsigned int, std::shared_ptr<typename Tree::tree>, T1,
                   std::shared_ptr<typename Tree::tree>, T1>
                F0>
  T1 tree_rec(F0 &&f, const T1 f0,
              const std::shared_ptr<typename Tree::tree> t) {
    return std::visit(
        Overloaded{[&](const typename Tree::Node _args) -> T1 {
                     unsigned int k = _args._a0;
                     std::shared_ptr<typename Tree::tree> t0 = _args._a1;
                     std::shared_ptr<typename Tree::tree> t1 = _args._a2;
                     return f(k, t0, tree_rec<T1>(f, f0, t0), t1,
                              tree_rec<T1>(f, f0, t1));
                   },
                   [&](const typename Tree::Leaf _args) -> T1 { return f0; }},
        *t);
  }

  using priqueue = std::shared_ptr<
      typename List::list<std::shared_ptr<typename Tree::tree>>>;

  static inline const priqueue empty =
      List::nil<std::shared_ptr<typename Tree::tree>>::make();

  static std::shared_ptr<typename Tree::tree>
  smash(const std::shared_ptr<typename Tree::tree> t,
        const std::shared_ptr<typename Tree::tree> u);

  static std::shared_ptr<
      typename List::list<std::shared_ptr<typename Tree::tree>>>
  carry(const std::shared_ptr<
            typename List::list<std::shared_ptr<typename Tree::tree>>>
            q,
        const std::shared_ptr<typename Tree::tree> t);

  static priqueue
  insert(const unsigned int x,
         const std::shared_ptr<
             typename List::list<std::shared_ptr<typename Tree::tree>>>
             q);

  static priqueue
  join(const std::shared_ptr<
           typename List::list<std::shared_ptr<typename Tree::tree>>>
           p,
       const std::shared_ptr<
           typename List::list<std::shared_ptr<typename Tree::tree>>>
           q,
       const std::shared_ptr<typename Tree::tree> c);

  template <
      MapsTo<std::shared_ptr<
                 typename List::list<std::shared_ptr<typename Tree::tree>>>,
             std::shared_ptr<
                 typename List::list<std::shared_ptr<typename Tree::tree>>>>
          F1>
  priqueue unzip(const std::shared_ptr<typename Tree::tree> t, F1 &&cont) {
    return std::visit(
        Overloaded{
            [&](const typename Tree::Node _args)
                -> std::shared_ptr<
                    typename List::list<std::shared_ptr<typename Tree::tree>>> {
              unsigned int x = _args._a0;
              std::shared_ptr<typename Tree::tree> t1 = _args._a1;
              std::shared_ptr<typename Tree::tree> t2 = _args._a2;
              std::function<std::shared_ptr<
                  typename List::list<std::shared_ptr<typename Tree::tree>>>(
                  std::shared_ptr<typename List::list<
                      std::shared_ptr<typename Tree::tree>>>)>
                  f = [&](std::shared_ptr<typename List::list<
                              std::shared_ptr<typename Tree::tree>>>
                              q) {
                    return List::cons<std::shared_ptr<typename Tree::tree>>::
                        make(Tree::Node::make(x, t1, Tree::Leaf::make()),
                             cont(q));
                  };
              return unzip(t2, f);
            },
            [&](const typename Tree::Leaf _args)
                -> std::shared_ptr<
                    typename List::list<std::shared_ptr<typename Tree::tree>>> {
              return cont(
                  List::nil<std::shared_ptr<typename Tree::tree>>::make());
            }},
        *t);
  }

  static priqueue heap_delete_max(const std::shared_ptr<typename Tree::tree> t);

  static key
  find_max_helper(const unsigned int current,
                  const std::shared_ptr<
                      typename List::list<std::shared_ptr<typename Tree::tree>>>
                      q);

  static std::optional<key>
  find_max(const std::shared_ptr<
           typename List::list<std::shared_ptr<typename Tree::tree>>>
               q);

  static std::pair<priqueue, priqueue>
  delete_max_aux(const unsigned int m,
                 const std::shared_ptr<
                     typename List::list<std::shared_ptr<typename Tree::tree>>>
                     p);

  static std::optional<std::pair<key, priqueue>>
  delete_max(const std::shared_ptr<
             typename List::list<std::shared_ptr<typename Tree::tree>>>
                 q);

  static priqueue
  merge(const std::shared_ptr<
            typename List::list<std::shared_ptr<typename Tree::tree>>>
            p,
        const std::shared_ptr<
            typename List::list<std::shared_ptr<typename Tree::tree>>>
            q);

  static priqueue
  insert_list(const std::shared_ptr<typename List::list<unsigned int>> l,
              const std::shared_ptr<
                  typename List::list<std::shared_ptr<typename Tree::tree>>>
                  q);

  static std::shared_ptr<typename List::list<unsigned int>>
  make_list(const unsigned int n,
            const std::shared_ptr<typename List::list<unsigned int>> l);

  static key help(const std::shared_ptr<
                  typename List::list<std::shared_ptr<typename Tree::tree>>>
                      c);

  static inline const key example1 = help(merge(
      insert(
          (((((0 + 1) + 1) + 1) + 1) + 1),
          insert(
              (((0 + 1) + 1) + 1),
              insert((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1),
                     List::nil<std::shared_ptr<typename Tree::tree>>::make()))),
      insert(
          (((0 + 1) + 1) + 1),
          insert(
              ((((((0 + 1) + 1) + 1) + 1) + 1) + 1),
              insert(
                  (((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1),
                  List::nil<std::shared_ptr<typename Tree::tree>>::make())))));

  static inline const key example2 = help(merge(
      insert_list(
          make_list(
              ((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1),
              List::nil<unsigned int>::make()),
          List::nil<std::shared_ptr<typename Tree::tree>>::make()),
      insert_list(
          make_list(
              (((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
               1),
              List::nil<unsigned int>::make()),
          List::nil<std::shared_ptr<typename Tree::tree>>::make())));
};
