#ifndef INCLUDED_DEEP_MAP
#define INCLUDED_DEEP_MAP

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

struct DeepMap {
  template <typename t_A> struct tree {
    // TYPES
    struct Leaf {};

    struct Node {
      std::unique_ptr<tree<t_A>> d_a0;
      t_A d_a1;
      std::unique_ptr<tree<t_A>> d_a2;
    };

    using variant_t = std::variant<Leaf, Node>;
    using crane_element_type = t_A;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    tree() {}

    explicit tree(Leaf _v) : d_v_(_v) {}

    explicit tree(Node _v) : d_v_(std::move(_v)) {}

    tree(const tree<t_A> &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    tree(tree<t_A> &&_other) : d_v_(std::move(_other.d_v_)) {}

    __attribute__((pure)) tree<t_A> &operator=(const tree<t_A> &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    __attribute__((pure)) tree<t_A> &operator=(tree<t_A> &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) tree<t_A> clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<Leaf>(_sv.v())) {
        return tree<t_A>(Leaf{});
      } else {
        const auto &[d_a0, d_a1, d_a2] = std::get<Node>(_sv.v());
        return tree<t_A>(
            Node{clone_value(d_a0), clone_value(d_a1), clone_value(d_a2)});
      }
    }

    // CREATORS
    template <typename _U> explicit tree(const tree<_U> &_other) {
      if (std::holds_alternative<typename tree<_U>::Leaf>(_other.v())) {
        d_v_ = Leaf{};
      } else {
        const auto &[d_a0, d_a1, d_a2] =
            std::get<typename tree<_U>::Node>(_other.v());
        d_v_ = Node{d_a0 ? std::make_unique<tree<t_A>>(*d_a0) : nullptr,
                    clone_as_value<t_A>(d_a1),
                    d_a2 ? std::make_unique<tree<t_A>>(*d_a2) : nullptr};
      }
    }

    __attribute__((pure)) static tree<t_A> leaf() { return tree(Leaf{}); }

    __attribute__((pure)) static tree<t_A> node(const tree<t_A> &a0, t_A a1,
                                                const tree<t_A> &a2) {
      return tree(Node{std::make_unique<tree<t_A>>(a0), std::move(a1),
                       std::make_unique<tree<t_A>>(a2)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) tree<t_A> *operator->() { return this; }

    __attribute__((pure)) const tree<t_A> *operator->() const { return this; }

    __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

    __attribute__((pure)) bool operator==(std::nullptr_t) const {
      return false;
    }

    // MANIPULATORS
    void reset() { *this = tree<t_A>(); }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, typename T2,
            MapsTo<T2, tree<T1>, T2, T1, tree<T1>, T2> F1>
  static T2 tree_rect(const T2 f, F1 &&f0, const tree<T1> &t) {
    if (std::holds_alternative<typename tree<T1>::Leaf>(t.v())) {
      return f;
    } else {
      const auto &[d_a0, d_a1, d_a2] = std::get<typename tree<T1>::Node>(t.v());
      return f0(*(d_a0), tree_rect<T1, T2>(f, f0, *(d_a0)), d_a1, *(d_a2),
                tree_rect<T1, T2>(f, f0, *(d_a2)));
    }
  }

  template <typename T1, typename T2,
            MapsTo<T2, tree<T1>, T2, T1, tree<T1>, T2> F1>
  static T2 tree_rec(const T2 f, F1 &&f0, const tree<T1> &t) {
    if (std::holds_alternative<typename tree<T1>::Leaf>(t.v())) {
      return f;
    } else {
      const auto &[d_a0, d_a1, d_a2] = std::get<typename tree<T1>::Node>(t.v());
      return f0(*(d_a0), tree_rec<T1, T2>(f, f0, *(d_a0)), d_a1, *(d_a2),
                tree_rec<T1, T2>(f, f0, *(d_a2)));
    }
  }

  /// Build a maximally-unbalanced tree (right spine = linked list).
  /// Tail-recursive via accumulator, should be loopified.
  __attribute__((pure)) static tree<unsigned int>
  build_right(unsigned int n, tree<unsigned int> acc);

  /// Recursive tree map — visits every node.
  template <typename T1, typename T2, MapsTo<T2, T1> F0>
  __attribute__((pure)) static tree<T2> tmap(F0 &&f, const tree<T1> &t) {
    if (std::holds_alternative<typename tree<T1>::Leaf>(t.v())) {
      return tree<T2>::leaf();
    } else {
      const auto &[d_a0, d_a1, d_a2] = std::get<typename tree<T1>::Node>(t.v());
      return tree<T2>::node(tmap<T1, T2>(f, *(d_a0)), f(d_a1),
                            tmap<T1, T2>(f, *(d_a2)));
    }
  }

  __attribute__((pure)) static tree<unsigned int>
  map_inc(const tree<unsigned int> &t);

  /// Get root value.
  __attribute__((pure)) static unsigned int
  root_or_zero(const tree<unsigned int> &t);
};

#endif // INCLUDED_DEEP_MAP
