#ifndef INCLUDED_HIGHER_KINDED
#define INCLUDED_HIGHER_KINDED

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

struct HigherKinded {
  template <typename T1, typename F0, typename F1>
  static T1 hk_map(F0 &&map_f, F1 &&f, const T1 x) {
    return map_f(f, x);
  }

  template <typename t_A> struct Tree {
    // TYPES
    struct Leaf {
      t_A d_a0;
    };

    struct Branch {
      std::shared_ptr<Tree<t_A>> d_a0;
      std::shared_ptr<Tree<t_A>> d_a1;
    };

    using variant_t = std::variant<Leaf, Branch>;

  private:
    // DATA
    variant_t d_v_;

    // CREATORS
    explicit Tree(Leaf _v) : d_v_(std::move(_v)) {}

    explicit Tree(Branch _v) : d_v_(std::move(_v)) {}

  public:
    // TYPES
    struct ctor {
      ctor() = delete;

      static std::shared_ptr<Tree<t_A>> Leaf_(t_A a0) {
        return std::shared_ptr<Tree<t_A>>(new Tree<t_A>(Leaf{a0}));
      }

      static std::shared_ptr<Tree<t_A>>
      Branch_(const std::shared_ptr<Tree<t_A>> &a0,
              const std::shared_ptr<Tree<t_A>> &a1) {
        return std::shared_ptr<Tree<t_A>>(new Tree<t_A>(Branch{a0, a1}));
      }

      static std::unique_ptr<Tree<t_A>> Leaf_uptr(t_A a0) {
        return std::unique_ptr<Tree<t_A>>(new Tree<t_A>(Leaf{a0}));
      }

      static std::unique_ptr<Tree<t_A>>
      Branch_uptr(const std::shared_ptr<Tree<t_A>> &a0,
                  const std::shared_ptr<Tree<t_A>> &a1) {
        return std::unique_ptr<Tree<t_A>>(new Tree<t_A>(Branch{a0, a1}));
      }
    };

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <
      typename T1, typename T2, MapsTo<T2, T1> F0,
      MapsTo<T2, std::shared_ptr<Tree<T1>>, T2, std::shared_ptr<Tree<T1>>, T2>
          F1>
  static T2 Tree_rect(F0 &&f, F1 &&f0, const std::shared_ptr<Tree<T1>> &t) {
    return std::visit(
        Overloaded{[&](const typename Tree<T1>::Leaf _args) -> T2 {
                     T1 y = _args.d_a0;
                     return f(y);
                   },
                   [&](const typename Tree<T1>::Branch _args) -> T2 {
                     std::shared_ptr<Tree<T1>> t0 = _args.d_a0;
                     std::shared_ptr<Tree<T1>> t1 = _args.d_a1;
                     return f0(t0, Tree_rect<T1, T2>(f, f0, t0), t1,
                               Tree_rect<T1, T2>(f, f0, t1));
                   }},
        t->v());
  }

  template <
      typename T1, typename T2, MapsTo<T2, T1> F0,
      MapsTo<T2, std::shared_ptr<Tree<T1>>, T2, std::shared_ptr<Tree<T1>>, T2>
          F1>
  static T2 Tree_rec(F0 &&f, F1 &&f0, const std::shared_ptr<Tree<T1>> &t) {
    return std::visit(
        Overloaded{[&](const typename Tree<T1>::Leaf _args) -> T2 {
                     T1 y = _args.d_a0;
                     return f(y);
                   },
                   [&](const typename Tree<T1>::Branch _args) -> T2 {
                     std::shared_ptr<Tree<T1>> t0 = _args.d_a0;
                     std::shared_ptr<Tree<T1>> t1 = _args.d_a1;
                     return f0(t0, Tree_rec<T1, T2>(f, f0, t0), t1,
                               Tree_rec<T1, T2>(f, f0, t1));
                   }},
        t->v());
  }

  template <typename T1, typename T2, MapsTo<T2, T1> F0>
  static std::shared_ptr<Tree<T2>>
  tree_map(F0 &&f, const std::shared_ptr<Tree<T1>> &t) {
    return std::visit(Overloaded{[&](const typename Tree<T1>::Leaf _args)
                                     -> std::shared_ptr<Tree<T2>> {
                                   T1 x = _args.d_a0;
                                   return Tree<T2>::ctor::Leaf_(f(x));
                                 },
                                 [&](const typename Tree<T1>::Branch _args)
                                     -> std::shared_ptr<Tree<T2>> {
                                   std::shared_ptr<Tree<T1>> l = _args.d_a0;
                                   std::shared_ptr<Tree<T1>> r = _args.d_a1;
                                   return Tree<T2>::ctor::Branch_(
                                       tree_map<T1, T2>(f, std::move(l)),
                                       tree_map<T1, T2>(f, std::move(r)));
                                 }},
                      t->v());
  }

  template <typename T1, typename T2, MapsTo<T2, T1> F0, MapsTo<T2, T2, T2> F1>
  static T2 tree_fold(F0 &&leaf_f, F1 &&branch_f,
                      const std::shared_ptr<Tree<T1>> &t) {
    return std::visit(
        Overloaded{[&](const typename Tree<T1>::Leaf _args) -> T2 {
                     T1 x = _args.d_a0;
                     return leaf_f(x);
                   },
                   [&](const typename Tree<T1>::Branch _args) -> T2 {
                     std::shared_ptr<Tree<T1>> l = _args.d_a0;
                     std::shared_ptr<Tree<T1>> r = _args.d_a1;
                     return branch_f(
                         tree_fold<T1, T2>(leaf_f, branch_f, std::move(l)),
                         tree_fold<T1, T2>(leaf_f, branch_f, std::move(r)));
                   }},
        t->v());
  }

  __attribute__((pure)) static unsigned int
  tree_sum(const std::shared_ptr<Tree<unsigned int>> &t);

  template <typename T1>
  __attribute__((pure)) static unsigned int
  tree_size(const std::shared_ptr<Tree<T1>> &t) {
    return tree_fold<T1, unsigned int>(
        [](T1 _x) { return 1u; },
        [](unsigned int _x0, unsigned int _x1) -> unsigned int {
          return (_x0 + _x1);
        },
        t);
  }

  template <typename T1, typename T2, MapsTo<T2, T1> F0>
  __attribute__((pure)) static std::optional<T2>
  map_option(F0 &&f, const std::optional<T1> o) {
    if (o.has_value()) {
      T1 x = *o;
      return std::make_optional<T2>(f(x));
    } else {
      return std::nullopt;
    }
  }

  static inline const std::shared_ptr<Tree<unsigned int>> test_tree =
      Tree<unsigned int>::ctor::Branch_(
          Tree<unsigned int>::ctor::Leaf_(1u),
          Tree<unsigned int>::ctor::Branch_(
              Tree<unsigned int>::ctor::Leaf_(2u),
              Tree<unsigned int>::ctor::Leaf_(3u)));
  static inline const unsigned int test_tree_sum = tree_sum(test_tree);
  static inline const unsigned int test_tree_size =
      tree_size<unsigned int>(test_tree);
  static inline const std::shared_ptr<Tree<unsigned int>> test_tree_map =
      tree_map<unsigned int, unsigned int>(
          [](unsigned int n) { return (n * 2u); }, test_tree);
  static inline const std::optional<unsigned int> test_hk_option = hk_map(
      []<typename _T1>(auto &&d_a0,
                       const std::optional<_T1> &d_a1) -> decltype(auto) {
        return map_option<_T1, std::invoke_result_t<decltype(d_a0) &, _T1 &>>(
            std::forward<decltype(d_a0)>(d_a0), d_a1);
      },
      [](unsigned int n) { return (n + 1u); },
      std::make_optional<unsigned int>(5u));
  static inline const std::shared_ptr<Tree<unsigned int>> test_hk_tree = hk_map(
      []<typename _T1>(auto &&d_a0, const std::shared_ptr<Tree<_T1>> &d_a1)
          -> decltype(auto) {
        return tree_map<_T1, std::invoke_result_t<decltype(d_a0) &, _T1 &>>(
            std::forward<decltype(d_a0)>(d_a0), d_a1);
      },
      [](unsigned int n) { return (n + 10u); }, test_tree);
};

#endif // INCLUDED_HIGHER_KINDED
