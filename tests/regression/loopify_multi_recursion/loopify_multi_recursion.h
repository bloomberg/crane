#ifndef INCLUDED_LOOPIFY_MULTI_RECURSION
#define INCLUDED_LOOPIFY_MULTI_RECURSION

#include <algorithm>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

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

struct LoopifyMultiRecursion {
  __attribute__((pure)) static unsigned int
  mixed_arith_fuel(const unsigned int &fuel, const unsigned int &n);
  __attribute__((pure)) static unsigned int mixed_arith(const unsigned int &n);
  __attribute__((pure)) static bool
  bool_or_chain_fuel(const unsigned int &fuel, const unsigned int &n,
                     const unsigned int &target);
  __attribute__((pure)) static unsigned int
  bool_or_chain(const unsigned int &n, const unsigned int &target);
  __attribute__((pure)) static bool
  bool_and_chain_fuel(const unsigned int &fuel, const unsigned int &n);
  __attribute__((pure)) static unsigned int
  bool_and_chain(const unsigned int &n);

  struct quadtree {
    // TYPES
    struct QLeaf {
      unsigned int d_a0;
    };

    struct QQuad {
      std::unique_ptr<quadtree> d_a0;
      std::unique_ptr<quadtree> d_a1;
      std::unique_ptr<quadtree> d_a2;
      std::unique_ptr<quadtree> d_a3;
    };

    using variant_t = std::variant<QLeaf, QQuad>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    quadtree() {}

    explicit quadtree(QLeaf _v) : d_v_(std::move(_v)) {}

    explicit quadtree(QQuad _v) : d_v_(std::move(_v)) {}

    quadtree(const quadtree &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    quadtree(quadtree &&_other) : d_v_(std::move(_other.d_v_)) {}

    __attribute__((pure)) quadtree &operator=(const quadtree &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    __attribute__((pure)) quadtree &operator=(quadtree &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) quadtree clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<QLeaf>(_sv.v())) {
        const auto &[d_a0] = std::get<QLeaf>(_sv.v());
        return quadtree(QLeaf{d_a0});
      } else {
        const auto &[d_a0, d_a1, d_a2, d_a3] = std::get<QQuad>(_sv.v());
        return quadtree(QQuad{clone_value(d_a0), clone_value(d_a1),
                              clone_value(d_a2), clone_value(d_a3)});
      }
    }

    // CREATORS
    __attribute__((pure)) static quadtree qleaf(unsigned int a0) {
      return quadtree(QLeaf{std::move(a0)});
    }

    __attribute__((pure)) static quadtree qquad(const quadtree &a0,
                                                const quadtree &a1,
                                                const quadtree &a2,
                                                const quadtree &a3) {
      return quadtree(QQuad{
          std::make_unique<quadtree>(a0), std::make_unique<quadtree>(a1),
          std::make_unique<quadtree>(a2), std::make_unique<quadtree>(a3)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) quadtree *operator->() { return this; }

    __attribute__((pure)) const quadtree *operator->() const { return this; }

    __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

    __attribute__((pure)) bool operator==(std::nullptr_t) const {
      return false;
    }

    // MANIPULATORS
    void reset() { *this = quadtree(); }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <
      typename T1, MapsTo<T1, unsigned int> F0,
      MapsTo<T1, quadtree, T1, quadtree, T1, quadtree, T1, quadtree, T1> F1>
  static T1 quadtree_rect(F0 &&f, F1 &&f0, const quadtree &q) {
    if (std::holds_alternative<typename quadtree::QLeaf>(q.v())) {
      const auto &[d_a0] = std::get<typename quadtree::QLeaf>(q.v());
      return f(d_a0);
    } else {
      const auto &[d_a0, d_a1, d_a2, d_a3] =
          std::get<typename quadtree::QQuad>(q.v());
      return f0(*(d_a0), quadtree_rect<T1>(f, f0, *(d_a0)), *(d_a1),
                quadtree_rect<T1>(f, f0, *(d_a1)), *(d_a2),
                quadtree_rect<T1>(f, f0, *(d_a2)), *(d_a3),
                quadtree_rect<T1>(f, f0, *(d_a3)));
    }
  }

  template <
      typename T1, MapsTo<T1, unsigned int> F0,
      MapsTo<T1, quadtree, T1, quadtree, T1, quadtree, T1, quadtree, T1> F1>
  static T1 quadtree_rec(F0 &&f, F1 &&f0, const quadtree &q) {
    if (std::holds_alternative<typename quadtree::QLeaf>(q.v())) {
      const auto &[d_a0] = std::get<typename quadtree::QLeaf>(q.v());
      return f(d_a0);
    } else {
      const auto &[d_a0, d_a1, d_a2, d_a3] =
          std::get<typename quadtree::QQuad>(q.v());
      return f0(*(d_a0), quadtree_rec<T1>(f, f0, *(d_a0)), *(d_a1),
                quadtree_rec<T1>(f, f0, *(d_a1)), *(d_a2),
                quadtree_rec<T1>(f, f0, *(d_a2)), *(d_a3),
                quadtree_rec<T1>(f, f0, *(d_a3)));
    }
  }

  __attribute__((pure)) static unsigned int
  quad_count_leaves(const quadtree &t);
  __attribute__((pure)) static unsigned int quad_depth(const quadtree &t);
  __attribute__((pure)) static unsigned int
  hofstadter_q_fuel(const unsigned int &fuel, const unsigned int &n);
  __attribute__((pure)) static unsigned int hofstadter_q(const unsigned int &n);
};

#endif // INCLUDED_LOOPIFY_MULTI_RECURSION
