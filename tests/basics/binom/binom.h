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

struct Priqueue {
  using key = unsigned int;

  struct tree {
  public:
    struct Node {
      key _a0;
      std::shared_ptr<tree> _a1;
      std::shared_ptr<tree> _a2;
    };
    struct Leaf {};
    using variant_t = std::variant<Node, Leaf>;

  private:
    variant_t v_;
    explicit tree(Node x) : v_(std::move(x)) {}
    explicit tree(Leaf x) : v_(std::move(x)) {}

  public:
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
    };
    const variant_t &v() const { return v_; }
  };

  template <typename T1, MapsTo<T1, unsigned int, std::shared_ptr<tree>, T1,
                                std::shared_ptr<tree>, T1>
                             F0>
  static T1 tree_rect(F0 &&f, const T1 f0, const std::shared_ptr<tree> &t) {
    return std::visit(
        Overloaded{[&](const typename tree::Node _args) -> T1 {
                     unsigned int k = _args._a0;
                     std::shared_ptr<tree> t0 = _args._a1;
                     std::shared_ptr<tree> t1 = _args._a2;
                     return f(k, t0, tree_rect<T1>(f, f0, t0), t1,
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
                     unsigned int k = _args._a0;
                     std::shared_ptr<tree> t0 = _args._a1;
                     std::shared_ptr<tree> t1 = _args._a2;
                     return f(k, t0, tree_rec<T1>(f, f0, t0), t1,
                              tree_rec<T1>(f, f0, t1));
                   },
                   [&](const typename tree::Leaf _args) -> T1 { return f0; }},
        t->v());
  }

  using priqueue = std::shared_ptr<List::list<std::shared_ptr<tree>>>;

  static inline const priqueue empty =
      List::list<std::shared_ptr<tree>>::ctor::nil_();

  static std::shared_ptr<tree> smash(const std::shared_ptr<tree> &t,
                                     const std::shared_ptr<tree> &u);

  static std::shared_ptr<List::list<std::shared_ptr<tree>>>
  carry(const std::shared_ptr<List::list<std::shared_ptr<tree>>> &q,
        const std::shared_ptr<tree> &t);

  static priqueue
  insert(const unsigned int x,
         const std::shared_ptr<List::list<std::shared_ptr<tree>>> &q);

  static priqueue
  join(const std::shared_ptr<List::list<std::shared_ptr<tree>>> &p,
       const std::shared_ptr<List::list<std::shared_ptr<tree>>> &q,
       const std::shared_ptr<tree> &c);

  template <MapsTo<std::shared_ptr<List::list<std::shared_ptr<tree>>>,
                   std::shared_ptr<List::list<std::shared_ptr<tree>>>>
                F1>
  static priqueue unzip(const std::shared_ptr<tree> &t, F1 &&cont) {
    return std::visit(
        Overloaded{
            [&](const typename tree::Node _args)
                -> std::shared_ptr<List::list<std::shared_ptr<tree>>> {
              unsigned int x = _args._a0;
              std::shared_ptr<tree> t1 = _args._a1;
              std::shared_ptr<tree> t2 = _args._a2;
              std::function<std::shared_ptr<List::list<std::shared_ptr<tree>>>(
                  std::shared_ptr<List::list<std::shared_ptr<tree>>>)>
                  f = [&](std::shared_ptr<List::list<std::shared_ptr<tree>>>
                              q) {
                    return List::list<std::shared_ptr<tree>>::ctor::cons_(
                        tree::ctor::Node_(x, t1, tree::ctor::Leaf_()), cont(q));
                  };
              return unzip(t2, f);
            },
            [&](const typename tree::Leaf _args)
                -> std::shared_ptr<List::list<std::shared_ptr<tree>>> {
              return cont(List::list<std::shared_ptr<tree>>::ctor::nil_());
            }},
        t->v());
  }

  static priqueue heap_delete_max(const std::shared_ptr<tree> &t);

  static key
  find_max_helper(const unsigned int current,
                  const std::shared_ptr<List::list<std::shared_ptr<tree>>> &q);

  static std::optional<key>
  find_max(const std::shared_ptr<List::list<std::shared_ptr<tree>>> &q);

  static std::pair<priqueue, priqueue>
  delete_max_aux(const unsigned int m,
                 const std::shared_ptr<List::list<std::shared_ptr<tree>>> &p);

  static std::optional<std::pair<key, priqueue>>
  delete_max(const std::shared_ptr<List::list<std::shared_ptr<tree>>> &q);

  static priqueue
  merge(const std::shared_ptr<List::list<std::shared_ptr<tree>>> &p,
        const std::shared_ptr<List::list<std::shared_ptr<tree>>> &q);

  static priqueue
  insert_list(const std::shared_ptr<List::list<unsigned int>> &l,
              const std::shared_ptr<List::list<std::shared_ptr<tree>>> &q);

  static std::shared_ptr<List::list<unsigned int>>
  make_list(const unsigned int n,
            const std::shared_ptr<List::list<unsigned int>> &l);

  static key help(const std::shared_ptr<List::list<std::shared_ptr<tree>>> &c);

  static inline const key example1 = help(merge(
      insert((((((0 + 1) + 1) + 1) + 1) + 1),
             insert((((0 + 1) + 1) + 1),
                    insert((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1),
                           List::list<std::shared_ptr<tree>>::ctor::nil_()))),
      insert(
          (((0 + 1) + 1) + 1),
          insert(((((((0 + 1) + 1) + 1) + 1) + 1) + 1),
                 insert((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1),
                        List::list<std::shared_ptr<tree>>::ctor::nil_())))));

  static inline const key example2 = help(merge(
      insert_list(
          make_list(
              ((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1),
              List::list<unsigned int>::ctor::nil_()),
          List::list<std::shared_ptr<tree>>::ctor::nil_()),
      insert_list(
          make_list(
              (((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
               1),
              List::list<unsigned int>::ctor::nil_()),
          List::list<std::shared_ptr<tree>>::ctor::nil_())));
};
