#ifndef INCLUDED_MUTUAL_RECURSION
#define INCLUDED_MUTUAL_RECURSION

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

struct MutualRecursion {
  __attribute__((pure)) static bool is_even(const unsigned int n);
  __attribute__((pure)) static bool is_odd(const unsigned int n);
  template <typename t_A> struct tree;
  template <typename t_A> struct forest;

  template <typename t_A> struct tree {
    // TYPES
    struct Leaf {
      t_A d_a0;
    };

    struct Node {
      std::shared_ptr<forest<t_A>> d_a0;
    };

    using variant_t = std::variant<Leaf, Node>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    explicit tree(Leaf _v) : d_v_(std::move(_v)) {}

    explicit tree(Node _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<tree<t_A>> leaf(t_A a0) {
      return std::make_shared<tree<t_A>>(Leaf{std::move(a0)});
    }

    static std::shared_ptr<tree<t_A>>
    node(const std::shared_ptr<forest<t_A>> &a0) {
      return std::make_shared<tree<t_A>>(Node{a0});
    }

    static std::shared_ptr<tree<t_A>> node(std::shared_ptr<forest<t_A>> &&a0) {
      return std::make_shared<tree<t_A>>(Node{std::move(a0)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename t_A> struct forest {
    // TYPES
    struct Empty {};

    struct Trees {
      std::shared_ptr<tree<t_A>> d_a0;
      std::shared_ptr<forest<t_A>> d_a1;
    };

    using variant_t = std::variant<Empty, Trees>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    explicit forest(Empty _v) : d_v_(_v) {}

    explicit forest(Trees _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<forest<t_A>> empty() {
      return std::make_shared<forest<t_A>>(Empty{});
    }

    static std::shared_ptr<forest<t_A>>
    trees(const std::shared_ptr<tree<t_A>> &a0,
          const std::shared_ptr<forest<t_A>> &a1) {
      return std::make_shared<forest<t_A>>(Trees{a0, a1});
    }

    static std::shared_ptr<forest<t_A>>
    trees(std::shared_ptr<tree<t_A>> &&a0, std::shared_ptr<forest<t_A>> &&a1) {
      return std::make_shared<forest<t_A>>(Trees{std::move(a0), std::move(a1)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, typename T2, MapsTo<T2, T1> F0,
            MapsTo<T2, std::shared_ptr<forest<T1>>> F1>
  static T2 tree_rect(F0 &&f, F1 &&f0, const std::shared_ptr<tree<T1>> &t) {
    return std::visit(
        Overloaded{[&](const typename tree<T1>::Leaf &_args) -> T2 {
                     return f(_args.d_a0);
                   },
                   [&](const typename tree<T1>::Node &_args) -> T2 {
                     return f0(_args.d_a0);
                   }},
        t->v());
  }

  template <typename T1, typename T2, MapsTo<T2, T1> F0,
            MapsTo<T2, std::shared_ptr<forest<T1>>> F1>
  static T2 tree_rec(F0 &&f, F1 &&f0, const std::shared_ptr<tree<T1>> &t) {
    return std::visit(
        Overloaded{[&](const typename tree<T1>::Leaf &_args) -> T2 {
                     return f(_args.d_a0);
                   },
                   [&](const typename tree<T1>::Node &_args) -> T2 {
                     return f0(_args.d_a0);
                   }},
        t->v());
  }

  template <
      typename T1, typename T2,
      MapsTo<T2, std::shared_ptr<tree<T1>>, std::shared_ptr<forest<T1>>, T2> F1>
  static T2 forest_rect(const T2 f, F1 &&f0,
                        const std::shared_ptr<forest<T1>> &f1) {
    return std::visit(
        Overloaded{[&](const typename forest<T1>::Empty &) -> T2 { return f; },
                   [&](const typename forest<T1>::Trees &_args) -> T2 {
                     return f0(_args.d_a0, _args.d_a1,
                               forest_rect<T1, T2>(f, f0, _args.d_a1));
                   }},
        f1->v());
  }

  template <
      typename T1, typename T2,
      MapsTo<T2, std::shared_ptr<tree<T1>>, std::shared_ptr<forest<T1>>, T2> F1>
  static T2 forest_rec(const T2 f, F1 &&f0,
                       const std::shared_ptr<forest<T1>> &f1) {
    return std::visit(
        Overloaded{[&](const typename forest<T1>::Empty &) -> T2 { return f; },
                   [&](const typename forest<T1>::Trees &_args) -> T2 {
                     return f0(_args.d_a0, _args.d_a1,
                               forest_rec<T1, T2>(f, f0, _args.d_a1));
                   }},
        f1->v());
  }

  template <typename T1>
  __attribute__((pure)) static unsigned int
  tree_size(const std::shared_ptr<tree<T1>> &t) {
    return std::visit(
        Overloaded{
            [](const typename tree<T1>::Leaf &) -> unsigned int { return 1u; },
            [](const typename tree<T1>::Node &_args) -> unsigned int {
              return forest_size<T1>(_args.d_a0);
            }},
        t->v());
  }

  template <typename T1>
  __attribute__((pure)) static unsigned int
  forest_size(const std::shared_ptr<forest<T1>> &f) {
    return std::visit(
        Overloaded{[](const typename forest<T1>::Empty &) -> unsigned int {
                     return 0u;
                   },
                   [](const typename forest<T1>::Trees &_args) -> unsigned int {
                     return (tree_size<T1>(_args.d_a0) +
                             forest_size<T1>(_args.d_a1));
                   }},
        f->v());
  }

  __attribute__((pure)) static unsigned int
  tree_sum(const std::shared_ptr<tree<unsigned int>> &t);
  __attribute__((pure)) static unsigned int
  forest_sum(const std::shared_ptr<forest<unsigned int>> &f);
  static inline const bool test_even_0 = is_even(0u);
  static inline const bool test_even_4 = is_even(4u);
  static inline const bool test_odd_3 = is_odd(3u);
  static inline const bool test_odd_4 = is_odd(4u);
  static inline const std::shared_ptr<tree<unsigned int>> simple_tree =
      tree<unsigned int>::node(forest<unsigned int>::trees(
          tree<unsigned int>::leaf(1u),
          forest<unsigned int>::trees(tree<unsigned int>::leaf(2u),
                                      forest<unsigned int>::empty())));
  static inline const std::shared_ptr<tree<unsigned int>> nested_tree =
      tree<unsigned int>::node(forest<unsigned int>::trees(
          tree<unsigned int>::node(forest<unsigned int>::trees(
              tree<unsigned int>::leaf(3u), forest<unsigned int>::empty())),
          forest<unsigned int>::trees(tree<unsigned int>::leaf(4u),
                                      forest<unsigned int>::empty())));
  static inline const unsigned int test_size_simple =
      tree_size<unsigned int>(simple_tree);
  static inline const unsigned int test_size_nested =
      tree_size<unsigned int>(nested_tree);
  static inline const unsigned int test_sum_simple = tree_sum(simple_tree);
  static inline const unsigned int test_sum_nested = tree_sum(nested_tree);
};

#endif // INCLUDED_MUTUAL_RECURSION
