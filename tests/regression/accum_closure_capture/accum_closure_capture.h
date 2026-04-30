#ifndef INCLUDED_ACCUM_CLOSURE_CAPTURE
#define INCLUDED_ACCUM_CLOSURE_CAPTURE

#include <functional>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

struct AccumClosureCapture {
  /// Define fn_list BEFORE tree so fn_list is not a forward inductive.
  /// This lets extract_closures (tree -> fn_list) be methodified on tree,
  /// because fn_list in the return type is not blocked by forward-ref check.
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
    fn_list clone() const {
      fn_list _out{};

      struct _CloneFrame {
        const fn_list *_src;
        fn_list *_dst;
      };

      std::vector<_CloneFrame> _stack;
      _stack.push_back({this, &_out});
      while (!_stack.empty()) {
        auto _frame = _stack.back();
        _stack.pop_back();
        const fn_list *_src = _frame._src;
        fn_list *_dst = _frame._dst;
        if (std::holds_alternative<FNil>(_src->v())) {
          const auto &_alt = std::get<FNil>(_src->v());
          _dst->d_v_ = FNil{};
        } else {
          const auto &_alt = std::get<FCons>(_src->v());
          _dst->d_v_ = FCons{_alt.d_a0,
                             _alt.d_a1 ? std::make_unique<fn_list>() : nullptr};
          auto &_dst_alt = std::get<FCons>(_dst->d_v_);
          if (_alt.d_a1)
            _stack.push_back({_alt.d_a1.get(), _dst_alt.d_a1.get()});
        }
      }
      return _out;
    }

    // CREATORS
    static fn_list fnil() { return fn_list(FNil{}); }

    static fn_list fcons(std::function<unsigned int(unsigned int)> a0,
                         fn_list a1) {
      return fn_list(
          FCons{std::move(a0), std::make_unique<fn_list>(std::move(a1))});
    }

    // MANIPULATORS
    ~fn_list() {
      std::vector<std::unique_ptr<fn_list>> _stack;
      auto _drain = [&](fn_list &_node) {
        if (std::holds_alternative<FCons>(_node.d_v_)) {
          auto &_alt = std::get<FCons>(_node.d_v_);
          if (_alt.d_a1)
            _stack.push_back(std::move(_alt.d_a1));
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
    const variant_t &v() const { return d_v_; }

    unsigned int apply_all(unsigned int init) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename fn_list::FNil>(_sv.v())) {
        return init;
      } else {
        const auto &[d_a0, d_a1] = std::get<typename fn_list::FCons>(_sv.v());
        return (*(d_a1)).apply_all(d_a0(init));
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
    tree clone() const {
      tree _out{};

      struct _CloneFrame {
        const tree *_src;
        tree *_dst;
      };

      std::vector<_CloneFrame> _stack;
      _stack.push_back({this, &_out});
      while (!_stack.empty()) {
        auto _frame = _stack.back();
        _stack.pop_back();
        const tree *_src = _frame._src;
        tree *_dst = _frame._dst;
        if (std::holds_alternative<Leaf>(_src->v())) {
          const auto &_alt = std::get<Leaf>(_src->v());
          _dst->d_v_ = Leaf{};
        } else {
          const auto &_alt = std::get<Node>(_src->v());
          _dst->d_v_ =
              Node{_alt.d_a0 ? std::make_unique<tree>() : nullptr, _alt.d_a1,
                   _alt.d_a2 ? std::make_unique<tree>() : nullptr};
          auto &_dst_alt = std::get<Node>(_dst->d_v_);
          if (_alt.d_a0)
            _stack.push_back({_alt.d_a0.get(), _dst_alt.d_a0.get()});
          if (_alt.d_a2)
            _stack.push_back({_alt.d_a2.get(), _dst_alt.d_a2.get()});
        }
      }
      return _out;
    }

    // CREATORS
    static tree leaf() { return tree(Leaf{}); }

    static tree node(tree a0, unsigned int a1, tree a2) {
      return tree(Node{std::make_unique<tree>(std::move(a0)), std::move(a1),
                       std::make_unique<tree>(std::move(a2))});
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
    const variant_t &v() const { return d_v_; }

    /// BUG HYPOTHESIS: extract_closures is methodified on tree. The closures
    /// capture this (for tree_sum t) as a raw pointer. They are stored in
    /// fn_list. After extract_closures returns, the temporary tree is
    /// destroyed. Calling the closures from apply_all dereferences dangling
    /// this.
    fn_list extract_closures() const {
      tree _self = *(this);
      auto &&_sv = *(this);
      if (std::holds_alternative<typename tree::Leaf>(_sv.v())) {
        return fn_list::fnil();
      } else {
        auto &[d_a0, d_a1, d_a2] = std::get<typename tree::Node>(_sv.v());
        return fn_list::fcons(
            [=](const unsigned int &x) mutable {
              return (x + _self.tree_sum());
            },
            fn_list::fcons(
                [=](const unsigned int &x) mutable { return (x + d_a1); },
                fn_list::fcons(
                    [=](const unsigned int &x) mutable {
                      return (x + _self.tree_sum());
                    },
                    fn_list::fnil())));
      }
    }

    unsigned int tree_sum() const {
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

  /// test1: Create tree with sum=42, extract closures, apply to 0.
  /// Expected: 0 + 42 = 42, 42 + 20 = 62, 62 + 42 = 104.
  /// With dangling this, tree_sum reads garbage.
  static inline const unsigned int test1 = []() {
    fn_list fs = tree::node(tree::node(tree::leaf(), 10u, tree::leaf()), 20u,
                            tree::node(tree::leaf(), 12u, tree::leaf()))
                     .extract_closures();
    return std::move(fs).apply_all(0u);
  }();
  /// test2: Allocate a noise tree between extracting closures and applying
  /// them. Increases memory pressure on freed region.
  static inline const unsigned int test2 = []() {
    fn_list fs =
        tree::node(tree::leaf(), 100u, tree::leaf()).extract_closures();
    unsigned int noise =
        tree::node(tree::leaf(), 999u, tree::leaf()).tree_sum();
    return std::move(fs).apply_all(noise);
  }();
};

#endif // INCLUDED_ACCUM_CLOSURE_CAPTURE
