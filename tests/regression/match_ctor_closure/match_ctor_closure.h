#ifndef INCLUDED_MATCH_CTOR_CLOSURE
#define INCLUDED_MATCH_CTOR_CLOSURE

#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

struct MatchCtorClosure {
  struct tree {
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

    __attribute__((pure)) unsigned int sum_values(const unsigned int x) const {
      if (std::holds_alternative<typename tree::Leaf>(this->v())) {
        return x;
      } else {
        const auto &[d_a0, d_a1, d_a2] =
            std::get<typename tree::Node>(this->v());
        if (std::holds_alternative<typename tree::Leaf>(d_a0->v())) {
          return (d_a1 + x);
        } else {
          const auto &[d_a00, d_a10, d_a20] =
              std::get<typename tree::Node>(d_a0->v());
          if (std::holds_alternative<typename tree::Leaf>(d_a2->v())) {
            return (d_a10 + x);
          } else {
            const auto &[d_a01, d_a11, d_a21] =
                std::get<typename tree::Node>(d_a2->v());
            return (((d_a10 + d_a11) + d_a1) + x);
          }
        }
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

  struct fn_box {
    // TYPES
    struct Box {
      std::function<unsigned int(unsigned int)> d_a0;
    };

    using variant_t = std::variant<Box>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    explicit fn_box(Box _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<fn_box>
    box(std::function<unsigned int(unsigned int)> a0) {
      return std::make_shared<fn_box>(Box{std::move(a0)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    __attribute__((pure)) unsigned int apply_box(const unsigned int x) const {
      const auto &[d_a0] = std::get<typename fn_box::Box>(this->v());
      return d_a0(x);
    }

    template <typename T1,
              MapsTo<T1, std::function<unsigned int(unsigned int)>> F0>
    T1 fn_box_rec(F0 &&f) const {
      const auto &[d_a0] = std::get<typename fn_box::Box>(this->v());
      return f(d_a0);
    }

    template <typename T1,
              MapsTo<T1, std::function<unsigned int(unsigned int)>> F0>
    T1 fn_box_rect(F0 &&f) const {
      const auto &[d_a0] = std::get<typename fn_box::Box>(this->v());
      return f(d_a0);
    }
  };

  /// BUG HYPOTHESIS: Match arm stores a partial application (closure)
  /// in a constructor. The lambda captures a PATTERN VARIABLE (_args.d_a0)
  /// by & reference. When the visit lambda returns, _args is destroyed
  /// but the fn_box retains the closure with a dangling reference.
  static std::shared_ptr<fn_box> match_and_box(const std::shared_ptr<tree> &t);
  /// Clobber stack, then use the closure from the box.
  static inline const unsigned int bug_match_ctor = []() {
    std::shared_ptr<tree> t =
        tree::node(tree::node(tree::leaf(), 10u, tree::leaf()), 20u,
                   tree::node(tree::leaf(), 30u, tree::leaf()));
    std::shared_ptr<fn_box> b = match_and_box(std::move(t));
    return std::move(b)->apply_box(5u);
  }();
};

#endif // INCLUDED_MATCH_CTOR_CLOSURE
