#ifndef INCLUDED_BINOMIAL_HEAP
#define INCLUDED_BINOMIAL_HEAP

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

template <typename t_A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    t_A d_a0;
    std::shared_ptr<List<t_A>> d_a1;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t d_v_;

  // CREATORS
  explicit List(Nil _v) : d_v_(std::move(_v)) {}

  explicit List(Cons _v) : d_v_(std::move(_v)) {}

public:
  // TYPES
  struct ctor {
    ctor() = delete;

    static std::shared_ptr<List<t_A>> Nil_() {
      return std::shared_ptr<List<t_A>>(new List<t_A>(Nil{}));
    }

    static std::shared_ptr<List<t_A>>
    Cons_(t_A a0, const std::shared_ptr<List<t_A>> &a1) {
      return std::shared_ptr<List<t_A>>(new List<t_A>(Cons{a0, a1}));
    }

    static std::unique_ptr<List<t_A>> Nil_uptr() {
      return std::unique_ptr<List<t_A>>(new List<t_A>(Nil{}));
    }

    static std::unique_ptr<List<t_A>>
    Cons_uptr(t_A a0, const std::shared_ptr<List<t_A>> &a1) {
      return std::unique_ptr<List<t_A>>(new List<t_A>(Cons{a0, a1}));
    }
  };

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
};

struct BinomialHeap {
  using key = unsigned int;

  struct tree {
    // TYPES
    struct Node {
      key d_a0;
      std::shared_ptr<tree> d_a1;
      std::shared_ptr<tree> d_a2;
    };

    struct Leaf {};

    using variant_t = std::variant<Node, Leaf>;

  private:
    // DATA
    variant_t d_v_;

    // CREATORS
    explicit tree(Node _v) : d_v_(std::move(_v)) {}

    explicit tree(Leaf _v) : d_v_(std::move(_v)) {}

  public:
    // TYPES
    struct ctor {
      ctor() = delete;

      static std::shared_ptr<tree> Node_(key a0,
                                         const std::shared_ptr<tree> &a1,
                                         const std::shared_ptr<tree> &a2) {
        return std::shared_ptr<tree>(new tree(Node{a0, a1, a2}));
      }

      static std::shared_ptr<tree> Leaf_() {
        return std::shared_ptr<tree>(new tree(Leaf{}));
      }

      static std::unique_ptr<tree> Node_uptr(key a0,
                                             const std::shared_ptr<tree> &a1,
                                             const std::shared_ptr<tree> &a2) {
        return std::unique_ptr<tree>(new tree(Node{a0, a1, a2}));
      }

      static std::unique_ptr<tree> Leaf_uptr() {
        return std::unique_ptr<tree>(new tree(Leaf{}));
      }
    };

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, unsigned int, std::shared_ptr<tree>, T1,
                                std::shared_ptr<tree>, T1>
                             F0>
  static T1 tree_rect(F0 &&f, const T1 f0, const std::shared_ptr<tree> &t) {
    return std::visit(
        Overloaded{[&](const typename tree::Node _args) -> T1 {
                     unsigned int k = _args.d_a0;
                     std::shared_ptr<tree> t0 = _args.d_a1;
                     std::shared_ptr<tree> t1 = _args.d_a2;
                     return f(std::move(k), t0, tree_rect<T1>(f, f0, t0), t1,
                              tree_rect<T1>(f, f0, t1));
                   },
                   [&](const typename tree::Leaf _args) -> T1 { return f0; }},
        t->v());
  }

  template <typename T1, MapsTo<T1, unsigned int, std::shared_ptr<tree>, T1,
                                std::shared_ptr<tree>, T1>
                             F0>
  static T1 tree_rec(F0 &&f, const T1 f0, const std::shared_ptr<tree> &t) {
    return std::visit(
        Overloaded{[&](const typename tree::Node _args) -> T1 {
                     unsigned int k = _args.d_a0;
                     std::shared_ptr<tree> t0 = _args.d_a1;
                     std::shared_ptr<tree> t1 = _args.d_a2;
                     return f(std::move(k), t0, tree_rec<T1>(f, f0, t0), t1,
                              tree_rec<T1>(f, f0, t1));
                   },
                   [&](const typename tree::Leaf _args) -> T1 { return f0; }},
        t->v());
  }

  using priqueue = std::shared_ptr<List<std::shared_ptr<tree>>>;
  static inline const priqueue empty =
      List<std::shared_ptr<tree>>::ctor::Nil_();
  static std::shared_ptr<tree> smash(const std::shared_ptr<tree> &t,
                                     const std::shared_ptr<tree> &u);
  static std::shared_ptr<List<std::shared_ptr<tree>>>
  carry(const std::shared_ptr<List<std::shared_ptr<tree>>> &q,
        std::shared_ptr<tree> t);
  __attribute__((pure)) static priqueue
  insert(const unsigned int x,
         const std::shared_ptr<List<std::shared_ptr<tree>>> &q);
  __attribute__((pure)) static priqueue
  join(const std::shared_ptr<List<std::shared_ptr<tree>>> &p,
       const std::shared_ptr<List<std::shared_ptr<tree>>> &q,
       std::shared_ptr<tree> c);

  template <MapsTo<std::shared_ptr<List<std::shared_ptr<tree>>>,
                   std::shared_ptr<List<std::shared_ptr<tree>>>>
                F1>
  __attribute__((pure)) static priqueue unzip(const std::shared_ptr<tree> &t,
                                              F1 &&cont) {
    return std::visit(
        Overloaded{[&](const typename tree::Node _args)
                       -> std::shared_ptr<List<std::shared_ptr<tree>>> {
                     unsigned int x = _args.d_a0;
                     std::shared_ptr<tree> t1 = _args.d_a1;
                     std::shared_ptr<tree> t2 = _args.d_a2;
                     std::function<std::shared_ptr<List<std::shared_ptr<tree>>>(
                         std::shared_ptr<List<std::shared_ptr<tree>>>)>
                         f = [=](std::shared_ptr<List<std::shared_ptr<tree>>>
                                     q) mutable {
                           return List<std::shared_ptr<tree>>::ctor::Cons_(
                               tree::ctor::Node_(x, t1, tree::ctor::Leaf_()),
                               cont(q));
                         };
                     return unzip(std::move(t2), f);
                   },
                   [&](const typename tree::Leaf _args)
                       -> std::shared_ptr<List<std::shared_ptr<tree>>> {
                     return cont(List<std::shared_ptr<tree>>::ctor::Nil_());
                   }},
        t->v());
  }

  __attribute__((pure)) static priqueue
  heap_delete_max(const std::shared_ptr<tree> &t);
  __attribute__((pure)) static key
  find_max_helper(const unsigned int current,
                  const std::shared_ptr<List<std::shared_ptr<tree>>> &q);
  __attribute__((pure)) static std::optional<key>
  find_max(const std::shared_ptr<List<std::shared_ptr<tree>>> &q);
  __attribute__((pure)) static std::pair<priqueue, priqueue>
  delete_max_aux(const unsigned int m,
                 const std::shared_ptr<List<std::shared_ptr<tree>>> &p);
  __attribute__((pure)) static std::optional<std::pair<key, priqueue>>
  delete_max(const std::shared_ptr<List<std::shared_ptr<tree>>> &q);
  __attribute__((pure)) static priqueue
  merge(const std::shared_ptr<List<std::shared_ptr<tree>>> &p,
        const std::shared_ptr<List<std::shared_ptr<tree>>> &q);
  __attribute__((pure)) static priqueue
  insert_list(const std::shared_ptr<List<unsigned int>> &l,
              std::shared_ptr<List<std::shared_ptr<tree>>> q);
  static std::shared_ptr<List<unsigned int>>
  make_list(const unsigned int n, std::shared_ptr<List<unsigned int>> l);
  __attribute__((pure)) static key
  help(const std::shared_ptr<List<std::shared_ptr<tree>>> &c);
  static inline const key example1 = help(merge(
      insert(5u,
             insert(3u, insert(7u, List<std::shared_ptr<tree>>::ctor::Nil_()))),
      insert(
          3u,
          insert(6u, insert(9u, List<std::shared_ptr<tree>>::ctor::Nil_())))));
  static inline const key example2 =
      help(merge(insert_list(make_list(10u, List<unsigned int>::ctor::Nil_()),
                             List<std::shared_ptr<tree>>::ctor::Nil_()),
                 insert_list(make_list(11u, List<unsigned int>::ctor::Nil_()),
                             List<std::shared_ptr<tree>>::ctor::Nil_())));
};

#endif // INCLUDED_BINOMIAL_HEAP
