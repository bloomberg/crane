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

  template <typename A> struct tree;
  template <typename A> struct forest;
  template <typename A> struct tree {
  public:
    struct Leaf {
      A _a0;
    };
    struct Node {
      std::shared_ptr<forest<A>> _a0;
    };
    using variant_t = std::variant<Leaf, Node>;

  private:
    variant_t v_;
    explicit tree(Leaf _v) : v_(std::move(_v)) {}
    explicit tree(Node _v) : v_(std::move(_v)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<tree<A>> Leaf_(A a0) {
        return std::shared_ptr<tree<A>>(new tree<A>(Leaf{a0}));
      }
      static std::shared_ptr<tree<A>>
      Node_(const std::shared_ptr<forest<A>> &a0) {
        return std::shared_ptr<tree<A>>(new tree<A>(Node{a0}));
      }
      static std::unique_ptr<tree<A>> Leaf_uptr(A a0) {
        return std::unique_ptr<tree<A>>(new tree<A>(Leaf{a0}));
      }
      static std::unique_ptr<tree<A>>
      Node_uptr(const std::shared_ptr<forest<A>> &a0) {
        return std::unique_ptr<tree<A>>(new tree<A>(Node{a0}));
      }
    };
    const variant_t &v() const { return v_; }
    variant_t &v_mut() { return v_; }
  };
  template <typename A> struct forest {
  public:
    struct Empty {};
    struct Trees {
      std::shared_ptr<tree<A>> _a0;
      std::shared_ptr<forest<A>> _a1;
    };
    using variant_t = std::variant<Empty, Trees>;

  private:
    variant_t v_;
    explicit forest(Empty _v) : v_(std::move(_v)) {}
    explicit forest(Trees _v) : v_(std::move(_v)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<forest<A>> Empty_() {
        return std::shared_ptr<forest<A>>(new forest<A>(Empty{}));
      }
      static std::shared_ptr<forest<A>>
      Trees_(const std::shared_ptr<tree<A>> &a0,
             const std::shared_ptr<forest<A>> &a1) {
        return std::shared_ptr<forest<A>>(new forest<A>(Trees{a0, a1}));
      }
      static std::unique_ptr<forest<A>> Empty_uptr() {
        return std::unique_ptr<forest<A>>(new forest<A>(Empty{}));
      }
      static std::unique_ptr<forest<A>>
      Trees_uptr(const std::shared_ptr<tree<A>> &a0,
                 const std::shared_ptr<forest<A>> &a1) {
        return std::unique_ptr<forest<A>>(new forest<A>(Trees{a0, a1}));
      }
    };
    const variant_t &v() const { return v_; }
    variant_t &v_mut() { return v_; }
  };

  template <typename T1, typename T2, MapsTo<T2, T1> F0,
            MapsTo<T2, std::shared_ptr<forest<T1>>> F1>
  static T2 tree_rect(F0 &&f, F1 &&f0, const std::shared_ptr<tree<T1>> &t) {
    return std::visit(
        Overloaded{[&](const typename tree<T1>::Leaf _args) -> T2 {
                     T1 a = _args._a0;
                     return f(a);
                   },
                   [&](const typename tree<T1>::Node _args) -> T2 {
                     std::shared_ptr<forest<T1>> f1 = _args._a0;
                     return f0(std::move(f1));
                   }},
        t->v());
  }

  template <typename T1, typename T2, MapsTo<T2, T1> F0,
            MapsTo<T2, std::shared_ptr<forest<T1>>> F1>
  static T2 tree_rec(F0 &&f, F1 &&f0, const std::shared_ptr<tree<T1>> &t) {
    return std::visit(
        Overloaded{[&](const typename tree<T1>::Leaf _args) -> T2 {
                     T1 a = _args._a0;
                     return f(a);
                   },
                   [&](const typename tree<T1>::Node _args) -> T2 {
                     std::shared_ptr<forest<T1>> f1 = _args._a0;
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
              std::shared_ptr<tree<T1>> t = _args._a0;
              std::shared_ptr<forest<T1>> f2 = _args._a1;
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
              std::shared_ptr<tree<T1>> t = _args._a0;
              std::shared_ptr<forest<T1>> f2 = _args._a1;
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
                     std::shared_ptr<forest<T1>> f = _args._a0;
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
                     std::shared_ptr<tree<T1>> t = _args._a0;
                     std::shared_ptr<forest<T1>> rest = _args._a1;
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
