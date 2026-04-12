#ifndef INCLUDED_BINOMIAL_HEAP
#define INCLUDED_BINOMIAL_HEAP

#include <functional>
#include <memory>
#include <optional>
#include <type_traits>
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

public:
  // CREATORS
  explicit List(Nil _v) : d_v_(_v) {}

  explicit List(Cons _v) : d_v_(std::move(_v)) {}

  static std::shared_ptr<List<t_A>> nil() {
    return std::make_shared<List<t_A>>(Nil{});
  }

  static std::shared_ptr<List<t_A>> cons(t_A a0,
                                         const std::shared_ptr<List<t_A>> &a1) {
    return std::make_shared<List<t_A>>(Cons{std::move(a0), a1});
  }

  static std::shared_ptr<List<t_A>> cons(t_A a0,
                                         std::shared_ptr<List<t_A>> &&a1) {
    return std::make_shared<List<t_A>>(Cons{std::move(a0), std::move(a1)});
  }

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

  public:
    // CREATORS
    explicit tree(Node _v) : d_v_(std::move(_v)) {}

    explicit tree(Leaf _v) : d_v_(_v) {}

    static std::shared_ptr<tree> node(key a0, const std::shared_ptr<tree> &a1,
                                      const std::shared_ptr<tree> &a2) {
      return std::make_shared<tree>(Node{std::move(a0), a1, a2});
    }

    static std::shared_ptr<tree> node(key a0, std::shared_ptr<tree> &&a1,
                                      std::shared_ptr<tree> &&a2) {
      return std::make_shared<tree>(
          Node{std::move(a0), std::move(a1), std::move(a2)});
    }

    static std::shared_ptr<tree> leaf() {
      return std::make_shared<tree>(Leaf{});
    }

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
        Overloaded{[&](const typename tree::Node &_args) -> T1 {
                     return f(_args.d_a0, _args.d_a1,
                              tree_rect<T1>(f, f0, _args.d_a1), _args.d_a2,
                              tree_rect<T1>(f, f0, _args.d_a2));
                   },
                   [&](const typename tree::Leaf &) -> T1 { return f0; }},
        t->v());
  }

  template <typename T1, MapsTo<T1, unsigned int, std::shared_ptr<tree>, T1,
                                std::shared_ptr<tree>, T1>
                             F0>
  static T1 tree_rec(F0 &&f, const T1 f0, const std::shared_ptr<tree> &t) {
    return std::visit(
        Overloaded{[&](const typename tree::Node &_args) -> T1 {
                     return f(_args.d_a0, _args.d_a1,
                              tree_rec<T1>(f, f0, _args.d_a1), _args.d_a2,
                              tree_rec<T1>(f, f0, _args.d_a2));
                   },
                   [&](const typename tree::Leaf &) -> T1 { return f0; }},
        t->v());
  }

  using priqueue = std::shared_ptr<List<std::shared_ptr<tree>>>;
  static inline const priqueue empty = List<std::shared_ptr<tree>>::nil();
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
        Overloaded{
            [&](const typename tree::Node &_args)
                -> std::shared_ptr<List<std::shared_ptr<tree>>> {
              std::function<std::shared_ptr<List<std::shared_ptr<tree>>>(
                  std::shared_ptr<List<std::shared_ptr<tree>>>)>
                  f = [=](const std::shared_ptr<List<std::shared_ptr<tree>>>
                              &q) mutable {
                    return List<std::shared_ptr<tree>>::cons(
                        tree::node(_args.d_a0, _args.d_a1, tree::leaf()),
                        cont(q));
                  };
              return unzip(_args.d_a2, f);
            },
            [&](const typename tree::Leaf &)
                -> std::shared_ptr<List<std::shared_ptr<tree>>> {
              return cont(List<std::shared_ptr<tree>>::nil());
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
      insert(5u, insert(3u, insert(7u, List<std::shared_ptr<tree>>::nil()))),
      insert(3u, insert(6u, insert(9u, List<std::shared_ptr<tree>>::nil())))));
  static inline const key example2 =
      help(merge(insert_list(make_list(10u, List<unsigned int>::nil()),
                             List<std::shared_ptr<tree>>::nil()),
                 insert_list(make_list(11u, List<unsigned int>::nil()),
                             List<std::shared_ptr<tree>>::nil())));
};

#endif // INCLUDED_BINOMIAL_HEAP
