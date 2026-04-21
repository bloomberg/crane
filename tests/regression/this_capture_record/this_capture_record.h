#ifndef INCLUDED_THIS_CAPTURE_RECORD
#define INCLUDED_THIS_CAPTURE_RECORD

#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

struct ThisCaptureRecord {
  /// A methodified function stores this-capturing closures in a
  /// Rocq record (not option/pair/fn_list). The record fields hold
  /// closures that reference tree_sum, which becomes this->tree_sum()
  /// in C++. After the temporary tree is destroyed, the closures'
  /// raw this pointer dangles.
  ///
  /// Different escape mechanism: record fields.
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

  /// A second inductive to prevent tree_callbacks from being
  /// methodified on callback_rec instead of tree.
  struct tag {
    // TYPES
    struct MkTag {
      unsigned int d_a0;
    };

    using variant_t = std::variant<MkTag>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    explicit tag(MkTag _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<tag> mktag(unsigned int a0) {
      return std::make_shared<tag>(MkTag{std::move(a0)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    template <typename T1, MapsTo<T1, unsigned int> F0>
    T1 tag_rec(F0 &&f) const {
      const auto &[d_a0] = std::get<typename tag::MkTag>(this->v());
      return f(d_a0);
    }

    template <typename T1, MapsTo<T1, unsigned int> F0>
    T1 tag_rect(F0 &&f) const {
      const auto &[d_a0] = std::get<typename tag::MkTag>(this->v());
      return f(d_a0);
    }
  };

  struct callback_rec {
    std::function<unsigned int(unsigned int)> cr_add;
    std::function<unsigned int(unsigned int)> cr_mul;
  };

  /// Methodified on tree. The extra flag argument forces Crane to
  /// treat this as a multi-argument function (preventing eta-collapse).
  /// Returns a record whose fields are closures that capture this
  /// via =, this.
  static std::shared_ptr<callback_rec> tree_callbacks(std::shared_ptr<tree> t,
                                                      const unsigned int flag);
  /// test1: flag=0, tree_sum=5.
  /// cr_add(10) = 10 + 5 = 15, cr_mul(3) = 3 * 5 = 15.
  /// Total = 30.
  static inline const unsigned int test1 = []() {
    std::shared_ptr<callback_rec> cb =
        tree_callbacks(tree::node(tree::leaf(), 5u, tree::leaf()), 0u);
    return (cb->cr_add(10u) + cb->cr_mul(3u));
  }();
  /// test2: With noise to clobber memory.
  /// flag=0, tree_sum = 60. cr_add(0) = 60, cr_mul(1) = 60.
  /// Total = 120.
  static inline const unsigned int test2 = []() {
    std::shared_ptr<callback_rec> cb = tree_callbacks(
        tree::node(tree::node(tree::leaf(), 10u, tree::leaf()), 20u,
                   tree::node(tree::leaf(), 30u, tree::leaf())),
        0u);
    return (cb->cr_add(0u) + cb->cr_mul(1u));
  }();
  /// test3: flag=1, tree_sum=100. cr_mul(7) = tree_sum = 100.
  static inline const unsigned int test3 =
      tree_callbacks(tree::node(tree::leaf(), 100u, tree::leaf()), 1u)
          ->cr_mul(7u);
  /// Dummy use of tag to keep it around for extraction.
  static std::shared_ptr<tag> mk_tag(const unsigned int n);
};

#endif // INCLUDED_THIS_CAPTURE_RECORD
