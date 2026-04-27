#ifndef INCLUDED_LIST_CLOSURE_ESCAPE
#define INCLUDED_LIST_CLOSURE_ESCAPE

#include <functional>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

struct ListClosureEscape {
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
            Node{d_a0 ? std::make_unique<ListClosureEscape::tree>(d_a0->clone())
                      : nullptr,
                 d_a1,
                 d_a2 ? std::make_unique<ListClosureEscape::tree>(d_a2->clone())
                      : nullptr});
      }
    }

    // CREATORS
    __attribute__((pure)) static tree leaf() { return tree(Leaf{}); }

    __attribute__((pure)) static tree node(const tree &a0, unsigned int a1,
                                           const tree &a2) {
      return tree(Node{std::make_unique<tree>(a0), std::move(a1),
                       std::make_unique<tree>(a2)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) tree *operator->() { return this; }

    __attribute__((pure)) const tree *operator->() const { return this; }

    __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

    __attribute__((pure)) bool operator==(std::nullptr_t) const {
      return false;
    }

    // MANIPULATORS
    void reset() { *this = tree(); }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    __attribute__((pure)) unsigned int sum_values(unsigned int x) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename tree::Leaf>(_sv.v())) {
        return x;
      } else {
        const auto &[d_a0, d_a1, d_a2] = std::get<typename tree::Node>(_sv.v());
        auto &&_sv0 = *(d_a0);
        if (std::holds_alternative<typename tree::Leaf>(_sv0.v())) {
          return (d_a1 + x);
        } else {
          const auto &[d_a00, d_a10, d_a20] =
              std::get<typename tree::Node>(_sv0.v());
          auto &&_sv1 = *(d_a2);
          if (std::holds_alternative<typename tree::Leaf>(_sv1.v())) {
            return (d_a10 + x);
          } else {
            const auto &[d_a01, d_a11, d_a21] =
                std::get<typename tree::Node>(_sv1.v());
            return (((d_a10 + d_a11) + d_a1) + x);
          }
        }
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

  /// A simple list of closures.
  struct fn_list {
    // TYPES
    struct FNil {};

    struct FCons {
      std::function<unsigned int(unsigned int)> d_a0;
      std::unique_ptr<fn_list> d_a1;
    };

    using variant_t = std::variant<FNil, FCons>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    fn_list() {}

    explicit fn_list(FNil _v) : d_v_(_v) {}

    explicit fn_list(FCons _v) : d_v_(std::move(_v)) {}

    fn_list(const fn_list &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    fn_list(fn_list &&_other) : d_v_(std::move(_other.d_v_)) {}

    fn_list &operator=(const fn_list &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    fn_list &operator=(fn_list &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) fn_list clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<FNil>(_sv.v())) {
        return fn_list(FNil{});
      } else {
        const auto &[d_a0, d_a1] = std::get<FCons>(_sv.v());
        return fn_list(FCons{
            d_a0,
            d_a1 ? std::make_unique<ListClosureEscape::fn_list>(d_a1->clone())
                 : nullptr});
      }
    }

    // CREATORS
    __attribute__((pure)) static fn_list fnil() { return fn_list(FNil{}); }

    __attribute__((pure)) static fn_list
    fcons(std::function<unsigned int(unsigned int)> a0, const fn_list &a1) {
      return fn_list(FCons{std::move(a0), std::make_unique<fn_list>(a1)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) fn_list *operator->() { return this; }

    __attribute__((pure)) const fn_list *operator->() const { return this; }

    __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

    __attribute__((pure)) bool operator==(std::nullptr_t) const {
      return false;
    }

    // MANIPULATORS
    void reset() { *this = fn_list(); }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    __attribute__((pure)) unsigned int apply_first(unsigned int x) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename fn_list::FNil>(_sv.v())) {
        return x;
      } else {
        const auto &[d_a0, d_a1] = std::get<typename fn_list::FCons>(_sv.v());
        return d_a0(x);
      }
    }

    template <
        typename T1,
        MapsTo<T1, std::function<unsigned int(unsigned int)>, fn_list, T1> F1>
    T1 fn_list_rec(const T1 f, F1 &&f0) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename fn_list::FNil>(_sv.v())) {
        return f;
      } else {
        const auto &[d_a0, d_a1] = std::get<typename fn_list::FCons>(_sv.v());
        return f0(d_a0, *(d_a1), (*(d_a1)).template fn_list_rec<T1>(f, f0));
      }
    }

    template <
        typename T1,
        MapsTo<T1, std::function<unsigned int(unsigned int)>, fn_list, T1> F1>
    T1 fn_list_rect(const T1 f, F1 &&f0) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename fn_list::FNil>(_sv.v())) {
        return f;
      } else {
        const auto &[d_a0, d_a1] = std::get<typename fn_list::FCons>(_sv.v());
        return f0(d_a0, *(d_a1), (*(d_a1)).template fn_list_rect<T1>(f, f0));
      }
    }
  };

  /// BUG: partial applications stored in a custom list via FCons.
  /// Each lambda for (sum_values t_i) captures t_i by &.
  /// When build_fns returns, t1 and t2 are destroyed.
  __attribute__((pure)) static fn_list build_fns(tree t1, tree t2);
  static inline const unsigned int bug_list_clobber = []() {
    tree t1 = tree::node(tree::node(tree::leaf(), 10u, tree::leaf()), 20u,
                         tree::node(tree::leaf(), 30u, tree::leaf()));
    tree t2 = tree::node(tree::node(tree::leaf(), 77u, tree::leaf()), 88u,
                         tree::node(tree::leaf(), 99u, tree::leaf()));
    fn_list fns = build_fns(t1, t2);
    return fns.apply_first(0u);
  }();
};

#endif // INCLUDED_LIST_CLOSURE_ESCAPE
