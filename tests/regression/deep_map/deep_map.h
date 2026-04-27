#ifndef INCLUDED_DEEP_MAP
#define INCLUDED_DEEP_MAP

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

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
        t_A __c1;
        if constexpr (
            requires { d_a1 ? 0 : 0; } && requires { *d_a1; } &&
            requires { d_a1->clone(); } && requires { d_a1.get(); }) {
          using _E = std::remove_cvref_t<decltype(*d_a1)>;
          __c1 = d_a1 ? std::make_unique<_E>(d_a1->clone()) : nullptr;
        } else if constexpr (requires { d_a1.clone(); }) {
          __c1 = d_a1.clone();
        } else {
          __c1 = d_a1;
        }
        return tree<t_A>(
            Node{d_a0 ? std::make_unique<DeepMap::tree<t_A>>(d_a0->clone())
                      : nullptr,
                 std::move(__c1),
                 d_a2 ? std::make_unique<DeepMap::tree<t_A>>(d_a2->clone())
                      : nullptr});
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
                    [&]<typename _DstT = t_A>(auto &&__v) -> _DstT {
                      if constexpr (
                          requires { *__v; } &&
                          !requires { std::declval<_DstT>().get(); })
                        return _DstT(*__v);
                      else if constexpr (
                          !requires { *__v; } &&
                          requires { std::declval<_DstT>().get(); }) {
                        using _E = std::remove_pointer_t<
                            decltype(std::declval<_DstT>().get())>;
                        return std::make_unique<_E>(std::move(__v));
                      } else
                        return _DstT(__v);
                    }(d_a1),
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
