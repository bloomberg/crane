#ifndef INCLUDED_CLOSURE_PAIR_THIS
#define INCLUDED_CLOSURE_PAIR_THIS

#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

struct ClosurePairThis {
  struct tree : public std::enable_shared_from_this<tree> {
    // TYPES
    struct Leaf {};

    struct Node {
      std::shared_ptr<tree> d_a0;
      unsigned int d_a1;
      std::shared_ptr<tree> d_a2;
    };

    using variant_t = std::variant<Leaf, Node>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    explicit tree(Leaf _v) : d_v_(_v) {}

    explicit tree(Node _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<tree> leaf() {
      return std::make_shared<tree>(Leaf{});
    }

    static std::shared_ptr<tree> node(const std::shared_ptr<tree> &a0,
                                      unsigned int a1,
                                      const std::shared_ptr<tree> &a2) {
      return std::make_shared<tree>(Node{a0, std::move(a1), a2});
    }

    static std::shared_ptr<tree> node(std::shared_ptr<tree> &&a0,
                                      unsigned int a1,
                                      std::shared_ptr<tree> &&a2) {
      return std::make_shared<tree>(
          Node{std::move(a0), std::move(a1), std::move(a2)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

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
    get_fn_pair(const unsigned int flag) const {
      std::shared_ptr<tree> _self =
          std::const_pointer_cast<tree>(this->shared_from_this());
      if (flag <= 0) {
        return std::make_pair(
            [=](const unsigned int x) mutable {
              return (x + _self->tree_sum());
            },
            [=](const unsigned int x) mutable {
              return (_self->tree_sum() * x);
            });
      } else {
        unsigned int _x = flag - 1;
        return std::make_pair(
            [=](const unsigned int x) mutable {
              return (_self->tree_sum() + x);
            },
            [](const unsigned int x) { return x; });
      }
    }

    __attribute__((pure)) unsigned int tree_sum() const {
      if (std::holds_alternative<typename tree::Leaf>(this->v())) {
        return 0u;
      } else {
        const auto &[d_a0, d_a1, d_a2] =
            std::get<typename tree::Node>(this->v());
        return ((d_a0->tree_sum() + d_a1) + d_a2->tree_sum());
      }
    }

    template <typename T1, MapsTo<T1, std::shared_ptr<tree>, T1, unsigned int,
                                  std::shared_ptr<tree>, T1>
                               F1>
    T1 tree_rec(const T1 f, F1 &&f0) const {
      if (std::holds_alternative<typename tree::Leaf>(this->v())) {
        return f;
      } else {
        const auto &[d_a0, d_a1, d_a2] =
            std::get<typename tree::Node>(this->v());
        return f0(d_a0, d_a0->template tree_rec<T1>(f, f0), d_a1, d_a2,
                  d_a2->template tree_rec<T1>(f, f0));
      }
    }

    template <typename T1, MapsTo<T1, std::shared_ptr<tree>, T1, unsigned int,
                                  std::shared_ptr<tree>, T1>
                               F1>
    T1 tree_rect(const T1 f, F1 &&f0) const {
      if (std::holds_alternative<typename tree::Leaf>(this->v())) {
        return f;
      } else {
        const auto &[d_a0, d_a1, d_a2] =
            std::get<typename tree::Node>(this->v());
        return f0(d_a0, d_a0->template tree_rect<T1>(f, f0), d_a1, d_a2,
                  d_a2->template tree_rect<T1>(f, f0));
      }
    }
  };

  struct wrapper {
    // TYPES
    struct Wrap {
      std::shared_ptr<tree> d_a0;
    };

    using variant_t = std::variant<Wrap>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    explicit wrapper(Wrap _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<wrapper> wrap(const std::shared_ptr<tree> &a0) {
      return std::make_shared<wrapper>(Wrap{a0});
    }

    static std::shared_ptr<wrapper> wrap(std::shared_ptr<tree> &&a0) {
      return std::make_shared<wrapper>(Wrap{std::move(a0)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, std::shared_ptr<tree>> F0>
  static T1 wrapper_rect(F0 &&f, const std::shared_ptr<wrapper> &w) {
    const auto &[d_a0] = std::get<typename wrapper::Wrap>(w->v());
    return f(d_a0);
  }

  template <typename T1, MapsTo<T1, std::shared_ptr<tree>> F0>
  static T1 wrapper_rec(F0 &&f, const std::shared_ptr<wrapper> &w) {
    const auto &[d_a0] = std::get<typename wrapper::Wrap>(w->v());
    return f(d_a0);
  }

  /// test1: flag=0 on tree with sum=7. fst closure adds, snd multiplies.
  /// (3 + 7) + (7 * 2) = 10 + 14 = 24.
  static inline const unsigned int test1 = []() {
    std::pair<std::function<unsigned int(unsigned int)>,
              std::function<unsigned int(unsigned int)>>
        p = tree::node(tree::leaf(), 7u, tree::leaf())->get_fn_pair(0u);
    return (p.first(3u) + p.second(2u));
  }();
  /// test2: flag=1. fst closure adds sum, snd is identity.
  /// (7 + 4) + 5 = 11 + 5 = 16.
  static inline const unsigned int test2 = []() {
    std::pair<std::function<unsigned int(unsigned int)>,
              std::function<unsigned int(unsigned int)>>
        p = tree::node(tree::leaf(), 7u, tree::leaf())->get_fn_pair(1u);
    return (p.first(4u) + p.second(5u));
  }();
  /// test3: Use both closures after allocating another tree to increase
  /// memory pressure on the freed region.
  static inline const unsigned int test3 = []() {
    std::pair<std::function<unsigned int(unsigned int)>,
              std::function<unsigned int(unsigned int)>>
        p = tree::node(tree::node(tree::leaf(), 3u, tree::leaf()), 5u,
                       tree::node(tree::leaf(), 2u, tree::leaf()))
                ->get_fn_pair(0u);
    unsigned int noise =
        tree::node(tree::leaf(), 999u, tree::leaf())->tree_sum();
    unsigned int a = p.first(noise);
    unsigned int b = p.second(1u);
    return (a + b);
  }();
};

#endif // INCLUDED_CLOSURE_PAIR_THIS
