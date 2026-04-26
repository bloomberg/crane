#ifndef INCLUDED_HIGHER_KINDED
#define INCLUDED_HIGHER_KINDED

#include <any>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

template <typename T> struct is_unique_ptr : std::false_type {};

template <typename T>
struct is_unique_ptr<std::unique_ptr<T>> : std::true_type {
  using element_type = T;
};

template <typename T> auto clone_value(const T &x) { return x; }

template <typename T>
std::unique_ptr<T> clone_value(const std::unique_ptr<T> &x) {
  if constexpr (requires { x->clone(); }) {
    return x ? std::make_unique<T>(x->clone()) : nullptr;
  } else {
    return x ? std::make_unique<T>(*x) : nullptr;
  }
}

template <typename Target, typename Source>
Target clone_as_value(const Source &x) {
  using T = std::remove_cvref_t<Target>;
  using S = std::remove_cvref_t<Source>;
  if constexpr (requires(const S &s) {
                  s.has_value();
                  *s;
                }) {
    if (!x.has_value())
      return T{};
    using TInner = std::remove_cvref_t<decltype(*std::declval<const T &>())>;
    return T{clone_as_value<TInner>(*x)};
  } else if constexpr (std::is_same_v<T, S>) {
    if constexpr (is_unique_ptr<T>::value) {
      return clone_value(x);
    } else if constexpr (requires { x.clone(); }) {
      return x.clone();
    } else {
      return x;
    }
  } else if constexpr (is_unique_ptr<S>::value) {
    if (!x)
      return T{};
    return clone_as_value<T>(*x);
  } else if constexpr (is_unique_ptr<T>::value) {
    using Inner = typename is_unique_ptr<T>::element_type;
    return std::make_unique<Inner>(clone_as_value<Inner>(x));
  } else {
    return T(x);
  }
}

struct HigherKinded {
  template <typename T1, typename T2 = void, typename T3 = void, typename F0,
            typename F1>
  static T1 hk_map(F0 &&map_f, F1 &&f, const T1 x) {
    return std::any_cast<T1>(map_f(f, x));
  }

  template <typename t_A> struct Tree {
    // TYPES
    struct Leaf {
      t_A d_a0;
    };

    struct Branch {
      std::unique_ptr<Tree<t_A>> d_a0;
      std::unique_ptr<Tree<t_A>> d_a1;
    };

    using variant_t = std::variant<Leaf, Branch>;
    using crane_element_type = t_A;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    Tree() {}

    explicit Tree(Leaf _v) : d_v_(std::move(_v)) {}

    explicit Tree(Branch _v) : d_v_(std::move(_v)) {}

    Tree(const Tree<t_A> &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    Tree(Tree<t_A> &&_other) : d_v_(std::move(_other.d_v_)) {}

    __attribute__((pure)) Tree<t_A> &operator=(const Tree<t_A> &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    __attribute__((pure)) Tree<t_A> &operator=(Tree<t_A> &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) Tree<t_A> clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<Leaf>(_sv.v())) {
        const auto &[d_a0] = std::get<Leaf>(_sv.v());
        return Tree<t_A>(Leaf{clone_value(d_a0)});
      } else {
        const auto &[d_a0, d_a1] = std::get<Branch>(_sv.v());
        return Tree<t_A>(Branch{clone_value(d_a0), clone_value(d_a1)});
      }
    }

    // CREATORS
    template <typename _U> explicit Tree(const Tree<_U> &_other) {
      if (std::holds_alternative<typename Tree<_U>::Leaf>(_other.v())) {
        const auto &[d_a0] = std::get<typename Tree<_U>::Leaf>(_other.v());
        d_v_ = Leaf{clone_as_value<t_A>(d_a0)};
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename Tree<_U>::Branch>(_other.v());
        d_v_ = Branch{d_a0 ? std::make_unique<Tree<t_A>>(*d_a0) : nullptr,
                      d_a1 ? std::make_unique<Tree<t_A>>(*d_a1) : nullptr};
      }
    }

    __attribute__((pure)) static Tree<t_A> leaf(t_A a0) {
      return Tree(Leaf{std::move(a0)});
    }

    __attribute__((pure)) static Tree<t_A> branch(const Tree<t_A> &a0,
                                                  const Tree<t_A> &a1) {
      return Tree(Branch{std::make_unique<Tree<t_A>>(a0),
                         std::make_unique<Tree<t_A>>(a1)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) Tree<t_A> *operator->() { return this; }

    __attribute__((pure)) const Tree<t_A> *operator->() const { return this; }

    __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

    __attribute__((pure)) bool operator==(std::nullptr_t) const {
      return false;
    }

    // MANIPULATORS
    void reset() { *this = Tree<t_A>(); }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, typename T2, MapsTo<T2, T1> F0,
            MapsTo<T2, Tree<T1>, T2, Tree<T1>, T2> F1>
  static T2 Tree_rect(F0 &&f, F1 &&f0, const Tree<T1> &t) {
    if (std::holds_alternative<typename Tree<T1>::Leaf>(t.v())) {
      const auto &[d_a0] = std::get<typename Tree<T1>::Leaf>(t.v());
      return f(d_a0);
    } else {
      const auto &[d_a0, d_a1] = std::get<typename Tree<T1>::Branch>(t.v());
      return f0(*(d_a0), Tree_rect<T1, T2>(f, f0, *(d_a0)), *(d_a1),
                Tree_rect<T1, T2>(f, f0, *(d_a1)));
    }
  }

  template <typename T1, typename T2, MapsTo<T2, T1> F0,
            MapsTo<T2, Tree<T1>, T2, Tree<T1>, T2> F1>
  static T2 Tree_rec(F0 &&f, F1 &&f0, const Tree<T1> &t) {
    if (std::holds_alternative<typename Tree<T1>::Leaf>(t.v())) {
      const auto &[d_a0] = std::get<typename Tree<T1>::Leaf>(t.v());
      return f(d_a0);
    } else {
      const auto &[d_a0, d_a1] = std::get<typename Tree<T1>::Branch>(t.v());
      return f0(*(d_a0), Tree_rec<T1, T2>(f, f0, *(d_a0)), *(d_a1),
                Tree_rec<T1, T2>(f, f0, *(d_a1)));
    }
  }

  template <typename T1, typename T2, MapsTo<T2, T1> F0>
  __attribute__((pure)) static Tree<T2> tree_map(F0 &&f, const Tree<T1> &t) {
    if (std::holds_alternative<typename Tree<T1>::Leaf>(t.v())) {
      const auto &[d_a0] = std::get<typename Tree<T1>::Leaf>(t.v());
      return Tree<T2>::leaf(f(d_a0));
    } else {
      const auto &[d_a0, d_a1] = std::get<typename Tree<T1>::Branch>(t.v());
      return Tree<T2>::branch(tree_map<T1, T2>(f, *(d_a0)),
                              tree_map<T1, T2>(f, *(d_a1)));
    }
  }

  template <typename T1, typename T2, MapsTo<T2, T1> F0, MapsTo<T2, T2, T2> F1>
  static T2 tree_fold(F0 &&leaf_f, F1 &&branch_f, const Tree<T1> &t) {
    if (std::holds_alternative<typename Tree<T1>::Leaf>(t.v())) {
      const auto &[d_a0] = std::get<typename Tree<T1>::Leaf>(t.v());
      return leaf_f(d_a0);
    } else {
      const auto &[d_a0, d_a1] = std::get<typename Tree<T1>::Branch>(t.v());
      return branch_f(tree_fold<T1, T2>(leaf_f, branch_f, *(d_a0)),
                      tree_fold<T1, T2>(leaf_f, branch_f, *(d_a1)));
    }
  }

  __attribute__((pure)) static unsigned int
  tree_sum(const Tree<unsigned int> &t);

  template <typename T1>
  __attribute__((pure)) static unsigned int tree_size(const Tree<T1> &t) {
    return tree_fold<T1, unsigned int>(
        [](const T1) { return 1u; },
        [](unsigned int _x0, unsigned int _x1) -> unsigned int {
          return (_x0 + _x1);
        },
        t);
  }

  template <typename T1, typename T2, MapsTo<T2, T1> F0>
  __attribute__((pure)) static std::optional<T2>
  map_option(F0 &&f, const std::optional<T1> &o) {
    if (o.has_value()) {
      const T1 &x = *o;
      return std::make_optional<T2>(f(x));
    } else {
      return std::optional<T2>();
    }
  }

  static inline const Tree<unsigned int> test_tree = Tree<unsigned int>::branch(
      Tree<unsigned int>::leaf(1u),
      Tree<unsigned int>::branch(Tree<unsigned int>::leaf(2u),
                                 Tree<unsigned int>::leaf(3u)));
  static inline const unsigned int test_tree_sum = tree_sum(test_tree);
  static inline const unsigned int test_tree_size =
      tree_size<unsigned int>(test_tree);
  static inline const Tree<unsigned int> test_tree_map =
      tree_map<unsigned int, unsigned int>(
          [](const unsigned int &n) { return (n * 2u); }, test_tree);
  static inline const std::optional<unsigned int> test_hk_option = hk_map(
      []<typename _T1>(auto &&d_a0,
                       const std::optional<_T1> &d_a1) -> decltype(auto) {
        return map_option<_T1, std::invoke_result_t<decltype(d_a0) &, _T1 &>>(
            std::forward<decltype(d_a0)>(d_a0), d_a1);
      },
      [](const unsigned int &n) { return (n + 1u); },
      std::make_optional<unsigned int>(5u));
  static inline const Tree<unsigned int> test_hk_tree = hk_map(
      []<typename _T1>(auto &&d_a0, const Tree<_T1> &d_a1) -> decltype(auto) {
        return tree_map<_T1, std::invoke_result_t<decltype(d_a0) &, _T1 &>>(
            std::forward<decltype(d_a0)>(d_a0), d_a1);
      },
      [](const unsigned int &n) { return (n + 10u); }, test_tree);
};

#endif // INCLUDED_HIGHER_KINDED
