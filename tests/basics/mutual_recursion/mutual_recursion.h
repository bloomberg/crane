#ifndef INCLUDED_MUTUAL_RECURSION
#define INCLUDED_MUTUAL_RECURSION

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

struct MutualRecursion {
  static bool is_even(const unsigned int n);
  static bool is_odd(const unsigned int n);
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

    // CREATORS
    explicit tree(Leaf _v) : d_v_(std::move(_v)) {}

    explicit tree(Node _v) : d_v_(std::move(_v)) {}

  public:
    // TYPES
    struct ctor {
      ctor() = delete;

      static std::shared_ptr<tree<t_A>> Leaf_(t_A a0) {
        return std::shared_ptr<tree<t_A>>(new tree<t_A>(Leaf{a0}));
      }

      static std::shared_ptr<tree<t_A>>
      Node_(const std::shared_ptr<forest<t_A>> &a0) {
        return std::shared_ptr<tree<t_A>>(new tree<t_A>(Node{a0}));
      }

      static std::unique_ptr<tree<t_A>> Leaf_uptr(t_A a0) {
        return std::unique_ptr<tree<t_A>>(new tree<t_A>(Leaf{a0}));
      }

      static std::unique_ptr<tree<t_A>>
      Node_uptr(const std::shared_ptr<forest<t_A>> &a0) {
        return std::unique_ptr<tree<t_A>>(new tree<t_A>(Node{a0}));
      }
    };

    // MANIPULATORS
    variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    const variant_t &v() const { return d_v_; }
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

    // CREATORS
    explicit forest(Empty _v) : d_v_(std::move(_v)) {}

    explicit forest(Trees _v) : d_v_(std::move(_v)) {}

  public:
    // TYPES
    struct ctor {
      ctor() = delete;

      static std::shared_ptr<forest<t_A>> Empty_() {
        return std::shared_ptr<forest<t_A>>(new forest<t_A>(Empty{}));
      }

      static std::shared_ptr<forest<t_A>>
      Trees_(const std::shared_ptr<tree<t_A>> &a0,
             const std::shared_ptr<forest<t_A>> &a1) {
        return std::shared_ptr<forest<t_A>>(new forest<t_A>(Trees{a0, a1}));
      }

      static std::unique_ptr<forest<t_A>> Empty_uptr() {
        return std::unique_ptr<forest<t_A>>(new forest<t_A>(Empty{}));
      }

      static std::unique_ptr<forest<t_A>>
      Trees_uptr(const std::shared_ptr<tree<t_A>> &a0,
                 const std::shared_ptr<forest<t_A>> &a1) {
        return std::unique_ptr<forest<t_A>>(new forest<t_A>(Trees{a0, a1}));
      }
    };

    // MANIPULATORS
    variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    const variant_t &v() const { return d_v_; }
  };

  template <typename T1, typename T2, MapsTo<T2, T1> F0,
            MapsTo<T2, std::shared_ptr<forest<T1>>> F1>
  static T2 tree_rect(F0 &&f, F1 &&f0, const std::shared_ptr<tree<T1>> &t) {
    return std::visit(
        Overloaded{[&](const typename tree<T1>::Leaf _args) -> T2 {
                     T1 a = _args.d_a0;
                     return f(a);
                   },
                   [&](const typename tree<T1>::Node _args) -> T2 {
                     std::shared_ptr<forest<T1>> f1 = _args.d_a0;
                     return f0(std::move(f1));
                   }},
        t->v());
  }

  template <typename T1, typename T2, MapsTo<T2, T1> F0,
            MapsTo<T2, std::shared_ptr<forest<T1>>> F1>
  static T2 tree_rec(F0 &&f, F1 &&f0, const std::shared_ptr<tree<T1>> &t) {
    return std::visit(
        Overloaded{[&](const typename tree<T1>::Leaf _args) -> T2 {
                     T1 a = _args.d_a0;
                     return f(a);
                   },
                   [&](const typename tree<T1>::Node _args) -> T2 {
                     std::shared_ptr<forest<T1>> f1 = _args.d_a0;
                     return f0(std::move(f1));
                   }},
        t->v());
  }

  template <
      typename T1, typename T2,
      MapsTo<T2, std::shared_ptr<tree<T1>>, std::shared_ptr<forest<T1>>, T2> F1>
  static T2 forest_rect(const T2 f, F1 &&f0,
                        const std::shared_ptr<forest<T1>> &f1) {
    return std::visit(
        Overloaded{
            [&](const typename forest<T1>::Empty _args) -> T2 { return f; },
            [&](const typename forest<T1>::Trees _args) -> T2 {
              std::shared_ptr<tree<T1>> t = _args.d_a0;
              std::shared_ptr<forest<T1>> f2 = _args.d_a1;
              return f0(std::move(t), f2, forest_rect<T1, T2>(f, f0, f2));
            }},
        f1->v());
  }

  template <
      typename T1, typename T2,
      MapsTo<T2, std::shared_ptr<tree<T1>>, std::shared_ptr<forest<T1>>, T2> F1>
  static T2 forest_rec(const T2 f, F1 &&f0,
                       const std::shared_ptr<forest<T1>> &f1) {
    return std::visit(
        Overloaded{
            [&](const typename forest<T1>::Empty _args) -> T2 { return f; },
            [&](const typename forest<T1>::Trees _args) -> T2 {
              std::shared_ptr<tree<T1>> t = _args.d_a0;
              std::shared_ptr<forest<T1>> f2 = _args.d_a1;
              return f0(std::move(t), f2, forest_rec<T1, T2>(f, f0, f2));
            }},
        f1->v());
  }

  template <typename T1>
  static unsigned int tree_size(const std::shared_ptr<tree<T1>> &t) {
    return std::visit(
        Overloaded{[](const typename tree<T1>::Leaf _args) -> unsigned int {
                     return 1u;
                   },
                   [](const typename tree<T1>::Node _args) -> unsigned int {
                     std::shared_ptr<forest<T1>> f = _args.d_a0;
                     return forest_size<T1>(std::move(f));
                   }},
        t->v());
  }

  template <typename T1>
  static unsigned int forest_size(const std::shared_ptr<forest<T1>> &f) {
    return std::visit(
        Overloaded{[](const typename forest<T1>::Empty _args) -> unsigned int {
                     return 0u;
                   },
                   [](const typename forest<T1>::Trees _args) -> unsigned int {
                     std::shared_ptr<tree<T1>> t = _args.d_a0;
                     std::shared_ptr<forest<T1>> rest = _args.d_a1;
                     return (tree_size<T1>(std::move(t)) +
                             forest_size<T1>(std::move(rest)));
                   }},
        f->v());
  }

  static unsigned int tree_sum(const std::shared_ptr<tree<unsigned int>> &t);
  static unsigned int
  forest_sum(const std::shared_ptr<forest<unsigned int>> &f);
  static inline const bool test_even_0 = is_even(0u);
  static inline const bool test_even_4 = is_even(4u);
  static inline const bool test_odd_3 = is_odd(3u);
  static inline const bool test_odd_4 = is_odd(4u);
  static inline const std::shared_ptr<tree<unsigned int>> simple_tree =
      tree<unsigned int>::ctor::Node_(forest<unsigned int>::ctor::Trees_(
          tree<unsigned int>::ctor::Leaf_(1u),
          forest<unsigned int>::ctor::Trees_(
              tree<unsigned int>::ctor::Leaf_(2u),
              forest<unsigned int>::ctor::Empty_())));
  static inline const std::shared_ptr<tree<unsigned int>> nested_tree =
      tree<unsigned int>::ctor::Node_(forest<unsigned int>::ctor::Trees_(
          tree<unsigned int>::ctor::Node_(forest<unsigned int>::ctor::Trees_(
              tree<unsigned int>::ctor::Leaf_(3u),
              forest<unsigned int>::ctor::Empty_())),
          forest<unsigned int>::ctor::Trees_(
              tree<unsigned int>::ctor::Leaf_(4u),
              forest<unsigned int>::ctor::Empty_())));
  static inline const unsigned int test_size_simple =
      tree_size<unsigned int>(simple_tree);
  static inline const unsigned int test_size_nested =
      tree_size<unsigned int>(nested_tree);
  static inline const unsigned int test_sum_simple = tree_sum(simple_tree);
  static inline const unsigned int test_sum_nested = tree_sum(nested_tree);
};

#endif // INCLUDED_MUTUAL_RECURSION
