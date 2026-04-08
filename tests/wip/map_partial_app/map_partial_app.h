#ifndef INCLUDED_MAP_PARTIAL_APP
#define INCLUDED_MAP_PARTIAL_APP

#include <functional>
#include <memory>
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
  explicit List(Nil _v) : d_v_(std::move(_v)) {}

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

  static std::unique_ptr<List<t_A>> nil_uptr() {
    return std::make_unique<List<t_A>>(Nil{});
  }

  static std::unique_ptr<List<t_A>>
  cons_uptr(t_A a0, const std::shared_ptr<List<t_A>> &a1) {
    return std::make_unique<List<t_A>>(Cons{std::move(a0), a1});
  }

  static std::unique_ptr<List<t_A>> cons_uptr(t_A a0,
                                              std::shared_ptr<List<t_A>> &&a1) {
    return std::make_unique<List<t_A>>(Cons{std::move(a0), std::move(a1)});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }

  template <typename T1, MapsTo<T1, t_A> F0>
  std::shared_ptr<List<T1>> map(F0 &&f) const {
    return std::visit(
        Overloaded{[](const typename List<t_A>::Nil _args)
                       -> std::shared_ptr<List<T1>> { return List<T1>::nil(); },
                   [&](const typename List<t_A>::Cons _args)
                       -> std::shared_ptr<List<T1>> {
                     return List<T1>::cons(f(_args.d_a0),
                                           _args.d_a1->template map<T1>(f));
                   }},
        this->v());
  }
};

struct MapPartialApp {
  struct tree {
    // TYPES
    struct Leaf {};

    struct Node {
      std::shared_ptr<tree> d_a0;
      unsigned int d_a1;
      std::shared_ptr<tree> d_a2;
    };

    using variant_t = std::variant<Leaf, Node>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    explicit tree(Leaf _v) : d_v_(std::move(_v)) {}

    explicit tree(Node _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<tree> leaf() {
      return std::make_shared<tree>(Leaf{});
    }

    static std::shared_ptr<tree> node(const std::shared_ptr<tree> &a0,
                                      unsigned int a1,
                                      const std::shared_ptr<tree> &a2) {
      return std::make_shared<tree>(Node{a0, std::move(a1), a2});
    }

    static std::shared_ptr<tree> node(std::shared_ptr<tree> &&a0,
                                      unsigned int a1,
                                      std::shared_ptr<tree> &&a2) {
      return std::make_shared<tree>(
          Node{std::move(a0), std::move(a1), std::move(a2)});
    }

    static std::unique_ptr<tree> leaf_uptr() {
      return std::make_unique<tree>(Leaf{});
    }

    static std::unique_ptr<tree> node_uptr(const std::shared_ptr<tree> &a0,
                                           unsigned int a1,
                                           const std::shared_ptr<tree> &a2) {
      return std::make_unique<tree>(Node{a0, std::move(a1), a2});
    }

    static std::unique_ptr<tree> node_uptr(std::shared_ptr<tree> &&a0,
                                           unsigned int a1,
                                           std::shared_ptr<tree> &&a2) {
      return std::make_unique<tree>(
          Node{std::move(a0), std::move(a1), std::move(a2)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, std::shared_ptr<tree>, T1, unsigned int,
                                std::shared_ptr<tree>, T1>
                             F1>
  static T1 tree_rect(const T1 f, F1 &&f0, const std::shared_ptr<tree> &t) {
    return std::visit(
        Overloaded{[&](const typename tree::Leaf _args) -> T1 { return f; },
                   [&](const typename tree::Node _args) -> T1 {
                     return f0(_args.d_a0, tree_rect<T1>(f, f0, _args.d_a0),
                               _args.d_a1, _args.d_a2,
                               tree_rect<T1>(f, f0, _args.d_a2));
                   }},
        t->v());
  }

  template <typename T1, MapsTo<T1, std::shared_ptr<tree>, T1, unsigned int,
                                std::shared_ptr<tree>, T1>
                             F1>
  static T1 tree_rec(const T1 f, F1 &&f0, const std::shared_ptr<tree> &t) {
    return std::visit(
        Overloaded{[&](const typename tree::Leaf _args) -> T1 { return f; },
                   [&](const typename tree::Node _args) -> T1 {
                     return f0(_args.d_a0, tree_rec<T1>(f, f0, _args.d_a0),
                               _args.d_a1, _args.d_a2,
                               tree_rec<T1>(f, f0, _args.d_a2));
                   }},
        t->v());
  }

  __attribute__((pure)) static unsigned int
  tree_sum(const std::shared_ptr<tree> &t);
  /// wrap: takes tree and nat, builds Node with leaves.
  static std::shared_ptr<tree> wrap(std::shared_ptr<tree> t,
                                    const unsigned int v);
  /// Sum a list of nats.
  __attribute__((pure)) static unsigned int
  sum_list(const std::shared_ptr<List<unsigned int>> &l);
  /// BUG HYPOTHESIS: Create a partial application (wrap t), store it,
  /// then apply it to multiple values from a list via map.
  /// The same closure is invoked repeatedly through list traversal.
  /// If std::move(t) is inside the lambda, first invocation moves t,
  /// subsequent ones get null.
  ///
  /// Expected:
  /// t = Node Leaf 10 Leaf (sum = 10)
  /// f = wrap t
  /// map (fun v => tree_sum (f v)) 1; 2; 3
  /// = tree_sum(Node(t,1,Leaf)); tree_sum(Node(t,2,Leaf));
  /// tree_sum(Node(t,3,Leaf)) = 10+1; 10+2; 10+3 = 11; 12; 13 sum_list 11; 12;
  /// 13 = 36
  static inline const unsigned int map_partial_bug = []() {
    return []() {
      std::unique_ptr<tree> t =
          tree::node_uptr(tree::leaf(), 10u, tree::leaf());
      std::function<std::shared_ptr<tree>(unsigned int)> f =
          [&](unsigned int _x0) -> std::shared_ptr<tree> {
        return wrap(std::move(t), _x0);
      };
      std::shared_ptr<List<unsigned int>> results =
          List<unsigned int>::cons(
              1u,
              List<unsigned int>::cons(
                  2u, List<unsigned int>::cons(3u, List<unsigned int>::nil())))
              ->template map<unsigned int>(
                  [=](unsigned int v) mutable { return tree_sum(f(v)); });
      return sum_list(std::move(results));
    }();
  }();
  /// Variation: store the partial app in a pair, extract it, then map.
  /// Extra indirection through pair.
  static inline const unsigned int map_partial_pair = []() {
    return []() {
      std::unique_ptr<tree> t =
          tree::node_uptr(tree::leaf(), 10u, tree::leaf());
      std::function<std::shared_ptr<tree>(unsigned int)> f =
          [&](unsigned int _x0) -> std::shared_ptr<tree> {
        return wrap(std::move(t), _x0);
      };
      std::pair<std::function<std::shared_ptr<tree>(unsigned int)>,
                unsigned int>
          p = std::make_pair(f, 0u);
      std::shared_ptr<List<unsigned int>> results =
          List<unsigned int>::cons(
              1u,
              List<unsigned int>::cons(
                  2u, List<unsigned int>::cons(3u, List<unsigned int>::nil())))
              ->template map<unsigned int>(
                  [=](unsigned int v) mutable { return tree_sum(p.first(v)); });
      return sum_list(std::move(results));
    }();
  }();
  /// Variation: two closures mapped over same list.
  static inline const unsigned int map_two_closures = []() {
    return []() {
      std::unique_ptr<tree> t1 =
          tree::node_uptr(tree::leaf(), 10u, tree::leaf());
      std::unique_ptr<tree> t2 =
          tree::node_uptr(tree::leaf(), 20u, tree::leaf());
      std::function<std::shared_ptr<tree>(unsigned int)> f1 =
          [&](unsigned int _x0) -> std::shared_ptr<tree> {
        return wrap(std::move(t1), _x0);
      };
      std::function<std::shared_ptr<tree>(unsigned int)> f2 =
          [&](unsigned int _x0) -> std::shared_ptr<tree> {
        return wrap(std::move(t2), _x0);
      };
      std::shared_ptr<List<unsigned int>> r1 =
          List<unsigned int>::cons(
              1u, List<unsigned int>::cons(2u, List<unsigned int>::nil()))
              ->template map<unsigned int>(
                  [=](unsigned int v) mutable { return tree_sum(f1(v)); });
      std::shared_ptr<List<unsigned int>> r2 =
          List<unsigned int>::cons(
              3u, List<unsigned int>::cons(4u, List<unsigned int>::nil()))
              ->template map<unsigned int>(
                  [=](unsigned int v) mutable { return tree_sum(f2(v)); });
      return (sum_list(std::move(r1)) + sum_list(std::move(r2)));
    }();
  }();
};

#endif // INCLUDED_MAP_PARTIAL_APP
