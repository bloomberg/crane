#ifndef INCLUDED_ACCUM_CLOSURE_CAPTURE
#define INCLUDED_ACCUM_CLOSURE_CAPTURE

#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

struct AccumClosureCapture {
  /// Define fn_list BEFORE tree so fn_list is not a forward inductive.
  /// This lets extract_closures (tree -> fn_list) be methodified on tree,
  /// because fn_list in the return type is not blocked by forward-ref check.
  struct fn_list {
    // TYPES
    struct FNil {};

    struct FCons {
      std::function<unsigned int(unsigned int)> d_a0;
      std::shared_ptr<fn_list> d_a1;
    };

    using variant_t = std::variant<FNil, FCons>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    explicit fn_list(FNil _v) : d_v_(_v) {}

    explicit fn_list(FCons _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<fn_list> fnil() {
      return std::make_shared<fn_list>(FNil{});
    }

    static std::shared_ptr<fn_list>
    fcons(std::function<unsigned int(unsigned int)> a0,
          const std::shared_ptr<fn_list> &a1) {
      return std::make_shared<fn_list>(FCons{std::move(a0), a1});
    }

    static std::shared_ptr<fn_list>
    fcons(std::function<unsigned int(unsigned int)> a0,
          std::shared_ptr<fn_list> &&a1) {
      return std::make_shared<fn_list>(FCons{std::move(a0), std::move(a1)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    __attribute__((pure)) unsigned int
    apply_all(const unsigned int init) const {
      if (std::holds_alternative<typename fn_list::FNil>(this->v())) {
        return init;
      } else {
        const auto &[d_a0, d_a1] = std::get<typename fn_list::FCons>(this->v());
        return d_a1->apply_all(d_a0(init));
      }
    }

    template <typename T1, MapsTo<T1, std::function<unsigned int(unsigned int)>,
                                  std::shared_ptr<fn_list>, T1>
                               F1>
    T1 fn_list_rec(const T1 f, F1 &&f0) const {
      if (std::holds_alternative<typename fn_list::FNil>(this->v())) {
        return f;
      } else {
        const auto &[d_a0, d_a1] = std::get<typename fn_list::FCons>(this->v());
        return f0(d_a0, d_a1, d_a1->template fn_list_rec<T1>(f, f0));
      }
    }

    template <typename T1, MapsTo<T1, std::function<unsigned int(unsigned int)>,
                                  std::shared_ptr<fn_list>, T1>
                               F1>
    T1 fn_list_rect(const T1 f, F1 &&f0) const {
      if (std::holds_alternative<typename fn_list::FNil>(this->v())) {
        return f;
      } else {
        const auto &[d_a0, d_a1] = std::get<typename fn_list::FCons>(this->v());
        return f0(d_a0, d_a1, d_a1->template fn_list_rect<T1>(f, f0));
      }
    }
  };

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

    /// BUG HYPOTHESIS: extract_closures is methodified on tree. The closures
    /// capture this (for tree_sum t) as a raw pointer. They are stored in
    /// fn_list. After extract_closures returns, the temporary tree is
    /// destroyed. Calling the closures from apply_all dereferences dangling
    /// this.
    std::shared_ptr<fn_list> extract_closures() const {
      std::shared_ptr<tree> _self =
          std::const_pointer_cast<tree>(this->shared_from_this());
      if (std::holds_alternative<typename tree::Leaf>(this->v())) {
        return fn_list::fnil();
      } else {
        const auto &[d_a0, d_a1, d_a2] =
            std::get<typename tree::Node>(this->v());
        return fn_list::fcons(
            [=](const unsigned int x) mutable {
              return (x + _self->tree_sum());
            },
            fn_list::fcons(
                [=](const unsigned int x) mutable { return (x + d_a1); },
                fn_list::fcons(
                    [=](const unsigned int x) mutable {
                      return (x + _self->tree_sum());
                    },
                    fn_list::fnil())));
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

  /// test1: Create tree with sum=42, extract closures, apply to 0.
  /// Expected: 0 + 42 = 42, 42 + 20 = 62, 62 + 42 = 104.
  /// With dangling this, tree_sum reads garbage.
  static inline const unsigned int test1 = []() {
    std::shared_ptr<fn_list> fs =
        tree::node(tree::node(tree::leaf(), 10u, tree::leaf()), 20u,
                   tree::node(tree::leaf(), 12u, tree::leaf()))
            ->extract_closures();
    return std::move(fs)->apply_all(0u);
  }();
  /// test2: Allocate a noise tree between extracting closures and applying
  /// them. Increases memory pressure on freed region.
  static inline const unsigned int test2 = []() {
    std::shared_ptr<fn_list> fs =
        tree::node(tree::leaf(), 100u, tree::leaf())->extract_closures();
    unsigned int noise =
        tree::node(tree::leaf(), 999u, tree::leaf())->tree_sum();
    return std::move(fs)->apply_all(noise);
  }();
};

#endif // INCLUDED_ACCUM_CLOSURE_CAPTURE
