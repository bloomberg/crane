#ifndef INCLUDED_CLOSURE_PAIR_THIS
#define INCLUDED_CLOSURE_PAIR_THIS

#include <functional>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

struct ClosurePairThis {
  struct tree {
    // TYPES
    struct Leaf {};

    struct Node {
      std::unique_ptr<tree> d_a0;
      unsigned int d_a1;
      std::unique_ptr<tree> d_a2;
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

    tree(const tree &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    tree(tree &&_other) : d_v_(std::move(_other.d_v_)) {}

    tree &operator=(const tree &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    tree &operator=(tree &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) tree clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<Leaf>(_sv.v())) {
        return tree(Leaf{});
      } else {
        const auto &[d_a0, d_a1, d_a2] = std::get<Node>(_sv.v());
        return tree(
            Node{d_a0 ? std::make_unique<ClosurePairThis::tree>(d_a0->clone())
                      : nullptr,
                 d_a1,
                 d_a2 ? std::make_unique<ClosurePairThis::tree>(d_a2->clone())
                      : nullptr});
      }
    }

    // CREATORS
    __attribute__((pure)) static tree leaf() { return tree(Leaf{}); }

    __attribute__((pure)) static tree node(tree a0, unsigned int a1, tree a2) {
      return tree(Node{std::make_unique<tree>(std::move(a0)), std::move(a1),
                       std::make_unique<tree>(std::move(a2))});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    /// BUG HYPOTHESIS: get_fn_pair returns two closures in a pair.
    /// When methodified, both closures capture the raw this pointer.
    /// The pair is custom-extracted as std::make_pair, so the closures
    /// are evaluated and stored while this is still valid.
    /// But after get_fn_pair returns, the temporary tree may be
    /// destroyed — calling either closure is then use-after-free.
    __attribute__((pure)) std::pair<std::function<unsigned int(unsigned int)>,
                                    std::function<unsigned int(unsigned int)>>
    get_fn_pair(const unsigned int &flag) const {
      tree _self = *(this);
      if (flag <= 0) {
        return std::make_pair(
            [=](const unsigned int &x) mutable {
              return (x + _self.tree_sum());
            },
            [=](const unsigned int &x) mutable {
              return (_self.tree_sum() * x);
            });
      } else {
        unsigned int _x = flag - 1;
        return std::make_pair(
            [=](const unsigned int &x) mutable {
              return (_self.tree_sum() + x);
            },
            [](unsigned int x) { return x; });
      }
    }

    __attribute__((pure)) unsigned int tree_sum() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename tree::Leaf>(_sv.v())) {
        return 0u;
      } else {
        const auto &[d_a0, d_a1, d_a2] = std::get<typename tree::Node>(_sv.v());
        return (((*(d_a0)).tree_sum() + d_a1) + (*(d_a2)).tree_sum());
      }
    }

    template <typename T1, MapsTo<T1, tree, T1, unsigned int, tree, T1> F1>
    T1 tree_rec(const T1 f, F1 &&f0) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename tree::Leaf>(_sv.v())) {
        return f;
      } else {
        const auto &[d_a0, d_a1, d_a2] = std::get<typename tree::Node>(_sv.v());
        return f0(*(d_a0), (*(d_a0)).template tree_rec<T1>(f, f0), d_a1,
                  *(d_a2), (*(d_a2)).template tree_rec<T1>(f, f0));
      }
    }

    template <typename T1, MapsTo<T1, tree, T1, unsigned int, tree, T1> F1>
    T1 tree_rect(const T1 f, F1 &&f0) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename tree::Leaf>(_sv.v())) {
        return f;
      } else {
        const auto &[d_a0, d_a1, d_a2] = std::get<typename tree::Node>(_sv.v());
        return f0(*(d_a0), (*(d_a0)).template tree_rect<T1>(f, f0), d_a1,
                  *(d_a2), (*(d_a2)).template tree_rect<T1>(f, f0));
      }
    }
  };

  struct wrapper {
    // TYPES
    struct Wrap {
      tree d_a0;
    };

    using variant_t = std::variant<Wrap>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    wrapper() {}

    explicit wrapper(Wrap _v) : d_v_(std::move(_v)) {}

    wrapper(const wrapper &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    wrapper(wrapper &&_other) : d_v_(std::move(_other.d_v_)) {}

    wrapper &operator=(const wrapper &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    wrapper &operator=(wrapper &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) wrapper clone() const {
      auto &&_sv = *(this);
      const auto &[d_a0] = std::get<Wrap>(_sv.v());
      return wrapper(Wrap{d_a0.clone()});
    }

    // CREATORS
    __attribute__((pure)) static wrapper wrap(tree a0) {
      return wrapper(Wrap{std::move(a0)});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, tree> F0>
  static T1 wrapper_rect(F0 &&f, const wrapper &w) {
    const auto &[d_a0] = std::get<typename wrapper::Wrap>(w.v());
    return f(d_a0);
  }

  template <typename T1, MapsTo<T1, tree> F0>
  static T1 wrapper_rec(F0 &&f, const wrapper &w) {
    const auto &[d_a0] = std::get<typename wrapper::Wrap>(w.v());
    return f(d_a0);
  }

  /// test1: flag=0 on tree with sum=7. fst closure adds, snd multiplies.
  /// (3 + 7) + (7 * 2) = 10 + 14 = 24.
  static inline const unsigned int test1 = []() {
    std::pair<std::function<unsigned int(unsigned int)>,
              std::function<unsigned int(unsigned int)>>
        p = tree::node(tree::leaf(), 7u, tree::leaf()).get_fn_pair(0u);
    return (p.first(3u) + p.second(2u));
  }();
  /// test2: flag=1. fst closure adds sum, snd is identity.
  /// (7 + 4) + 5 = 11 + 5 = 16.
  static inline const unsigned int test2 = []() {
    std::pair<std::function<unsigned int(unsigned int)>,
              std::function<unsigned int(unsigned int)>>
        p = tree::node(tree::leaf(), 7u, tree::leaf()).get_fn_pair(1u);
    return (p.first(4u) + p.second(5u));
  }();
  /// test3: Use both closures after allocating another tree to increase
  /// memory pressure on the freed region.
  static inline const unsigned int test3 = []() {
    std::pair<std::function<unsigned int(unsigned int)>,
              std::function<unsigned int(unsigned int)>>
        p = tree::node(tree::node(tree::leaf(), 3u, tree::leaf()), 5u,
                       tree::node(tree::leaf(), 2u, tree::leaf()))
                .get_fn_pair(0u);
    unsigned int noise =
        tree::node(tree::leaf(), 999u, tree::leaf()).tree_sum();
    unsigned int a = p.first(noise);
    unsigned int b = p.second(1u);
    return (a + b);
  }();
};

#endif // INCLUDED_CLOSURE_PAIR_THIS
