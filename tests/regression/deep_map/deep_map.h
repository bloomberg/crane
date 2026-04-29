#ifndef INCLUDED_DEEP_MAP
#define INCLUDED_DEEP_MAP

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

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

    tree<t_A> &operator=(const tree<t_A> &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    tree<t_A> &operator=(tree<t_A> &&_other) {
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
            Node{d_a0 ? std::make_unique<DeepMap::tree<t_A>>(d_a0->clone())
                      : nullptr,
                 d_a1,
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
        d_v_ =
            Node{d_a0 ? std::make_unique<tree<t_A>>(*d_a0) : nullptr, t_A(d_a1),
                 d_a2 ? std::make_unique<tree<t_A>>(*d_a2) : nullptr};
      }
    }

    __attribute__((pure)) static tree<t_A> leaf() { return tree(Leaf{}); }

    __attribute__((pure)) static tree<t_A> node(tree<t_A> a0, t_A a1,
                                                tree<t_A> a2) {
      return tree(Node{std::make_unique<tree<t_A>>(std::move(a0)),
                       std::move(a1),
                       std::make_unique<tree<t_A>>(std::move(a2))});
    }

    // MANIPULATORS
    ~tree() {
      std::vector<std::unique_ptr<tree>> _stack;
      auto _drain = [&](tree &_node) {
        if (std::holds_alternative<Node>(_node.d_v_)) {
          auto &_alt = std::get<Node>(_node.d_v_);
          if (_alt.d_a0)
            _stack.push_back(std::move(_alt.d_a0));
          if (_alt.d_a2)
            _stack.push_back(std::move(_alt.d_a2));
        }
      };
      _drain(*this);
      while (!_stack.empty()) {
        auto _node = std::move(_stack.back());
        _stack.pop_back();
        if (_node)
          _drain(*_node);
      }
    }

    inline variant_t &v_mut() { return d_v_; }

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
