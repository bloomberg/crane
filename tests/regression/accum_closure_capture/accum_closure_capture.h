#ifndef INCLUDED_ACCUM_CLOSURE_CAPTURE
#define INCLUDED_ACCUM_CLOSURE_CAPTURE

#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

struct AccumClosureCapture {
  /// Define fn_list BEFORE tree so fn_list is not a forward inductive.
  /// This lets extract_closures (tree -> fn_list) be methodified on tree,
  /// because fn_list in the return type is not blocked by forward-ref check.
  struct fn_list {
    // TYPES
    struct FNil {};

    struct FCons {
      std::function<uint64_t(uint64_t)> a0;
      std::unique_ptr<fn_list> a1;
    };

    using variant_t = std::variant<FNil, FCons>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    fn_list() {}

    explicit fn_list(FNil _v) : v_(_v) {}

    explicit fn_list(FCons _v) : v_(std::move(_v)) {}

    fn_list(const fn_list &_other) : v_(std::move(_other.clone().v_)) {}

    fn_list(fn_list &&_other) noexcept : v_(std::move(_other.v_)) {}

    fn_list &operator=(const fn_list &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    fn_list &operator=(fn_list &&_other) noexcept {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    fn_list clone() const {
      fn_list _out{};

      struct _CloneFrame {
        const fn_list *_src;
        fn_list *_dst;
      };

      std::vector<_CloneFrame> _stack{};
      _stack.reserve(8);
      _stack.push_back({this, &_out});
      while (!_stack.empty()) {
        auto _frame = _stack.back();
        _stack.pop_back();
        const fn_list *_src = _frame._src;
        fn_list *_dst = _frame._dst;
        if (std::holds_alternative<FNil>(_src->v())) {
          _dst->v_ = FNil{};
        } else {
          const auto &_alt = std::get<FCons>(_src->v());
          _dst->v_ =
              FCons{_alt.a0, _alt.a1 ? std::make_unique<fn_list>() : nullptr};
          auto &_dst_alt = std::get<FCons>(_dst->v_);
          if (_alt.a1) {
            _stack.push_back({_alt.a1.get(), _dst_alt.a1.get()});
          }
        }
      }
      return _out;
    }

    // CREATORS
    static fn_list fnil() { return fn_list(FNil{}); }

    static fn_list fcons(std::function<uint64_t(uint64_t)> a0, fn_list a1) {
      return fn_list(
          FCons{std::move(a0), std::make_unique<fn_list>(std::move(a1))});
    }

    // MANIPULATORS
    ~fn_list() {
      std::vector<std::unique_ptr<fn_list>> _stack{};
      _stack.reserve(8);
      auto _drain = [&](fn_list &_node) {
        if (std::holds_alternative<FCons>(_node.v_)) {
          auto &_alt = std::get<FCons>(_node.v_);
          if (_alt.a1) {
            _stack.push_back(std::move(_alt.a1));
          }
        }
      };
      _drain(*this);
      while (!_stack.empty()) {
        auto _node = std::move(_stack.back());
        _stack.pop_back();
        if (_node) {
          _drain(*_node);
        }
      }
    }

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    uint64_t apply_all(uint64_t init) const {
      if (std::holds_alternative<typename fn_list::FNil>(this->v())) {
        return init;
      } else {
        const auto &[a0, a1] = std::get<typename fn_list::FCons>(this->v());
        return a1->apply_all(a0(init));
      }
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<
          T1, F1 &, std::function<uint64_t(uint64_t)> &, fn_list &, T1 &>
    T1 fn_list_rec(T1 f, F1 &&f0) const {
      if (std::holds_alternative<typename fn_list::FNil>(this->v())) {
        return f;
      } else {
        const auto &[a0, a1] = std::get<typename fn_list::FCons>(this->v());
        return f0(a0, *a1, a1->template fn_list_rec<T1>(f, f0));
      }
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<
          T1, F1 &, std::function<uint64_t(uint64_t)> &, fn_list &, T1 &>
    T1 fn_list_rect(T1 f, F1 &&f0) const {
      if (std::holds_alternative<typename fn_list::FNil>(this->v())) {
        return f;
      } else {
        const auto &[a0, a1] = std::get<typename fn_list::FCons>(this->v());
        return f0(a0, *a1, a1->template fn_list_rect<T1>(f, f0));
      }
    }
  };

  struct tree {
    // TYPES
    struct Leaf {};

    struct Node {
      std::unique_ptr<tree> a0;
      uint64_t a1;
      std::unique_ptr<tree> a2;
    };

    using variant_t = std::variant<Leaf, Node>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    tree() {}

    explicit tree(Leaf _v) : v_(_v) {}

    explicit tree(Node _v) : v_(std::move(_v)) {}

    tree(const tree &_other) : v_(std::move(_other.clone().v_)) {}

    tree(tree &&_other) noexcept : v_(std::move(_other.v_)) {}

    tree &operator=(const tree &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    tree &operator=(tree &&_other) noexcept {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    tree clone() const {
      tree _out{};

      struct _CloneFrame {
        const tree *_src;
        tree *_dst;
      };

      std::vector<_CloneFrame> _stack{};
      _stack.reserve(8);
      _stack.push_back({this, &_out});
      while (!_stack.empty()) {
        auto _frame = _stack.back();
        _stack.pop_back();
        const tree *_src = _frame._src;
        tree *_dst = _frame._dst;
        if (std::holds_alternative<Leaf>(_src->v())) {
          _dst->v_ = Leaf{};
        } else {
          const auto &_alt = std::get<Node>(_src->v());
          _dst->v_ = Node{_alt.a0 ? std::make_unique<tree>() : nullptr, _alt.a1,
                          _alt.a2 ? std::make_unique<tree>() : nullptr};
          auto &_dst_alt = std::get<Node>(_dst->v_);
          if (_alt.a0) {
            _stack.push_back({_alt.a0.get(), _dst_alt.a0.get()});
          }
          if (_alt.a2) {
            _stack.push_back({_alt.a2.get(), _dst_alt.a2.get()});
          }
        }
      }
      return _out;
    }

    // CREATORS
    static tree leaf() { return tree(Leaf{}); }

    static tree node(tree a0, uint64_t a1, tree a2) {
      return tree(Node{std::make_unique<tree>(std::move(a0)), a1,
                       std::make_unique<tree>(std::move(a2))});
    }

    // MANIPULATORS
    ~tree() {
      std::vector<std::unique_ptr<tree>> _stack{};
      _stack.reserve(8);
      auto _drain = [&](tree &_node) {
        if (std::holds_alternative<Node>(_node.v_)) {
          auto &_alt = std::get<Node>(_node.v_);
          if (_alt.a0) {
            _stack.push_back(std::move(_alt.a0));
          }
          if (_alt.a2) {
            _stack.push_back(std::move(_alt.a2));
          }
        }
      };
      _drain(*this);
      while (!_stack.empty()) {
        auto _node = std::move(_stack.back());
        _stack.pop_back();
        if (_node) {
          _drain(*_node);
        }
      }
    }

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    /// BUG HYPOTHESIS: extract_closures is methodified on tree. The closures
    /// capture this (for tree_sum t) as a raw pointer. They are stored in
    /// fn_list. After extract_closures returns, the temporary tree is
    /// destroyed. Calling the closures from apply_all dereferences dangling
    /// this.
    fn_list extract_closures() const {
      tree _self_val = *this;
      if (std::holds_alternative<typename tree::Leaf>(this->v())) {
        return fn_list::fnil();
      } else {
        auto &[a0, a1, a2] = std::get<typename tree::Node>(this->v());
        return fn_list::fcons(
            [=](uint64_t x) mutable { return (x + _self_val.tree_sum()); },
            fn_list::fcons([=](uint64_t x) mutable { return (x + a1); },
                           fn_list::fcons(
                               [=](uint64_t x) mutable {
                                 return (x + _self_val.tree_sum());
                               },
                               fn_list::fnil())));
      }
    }

    uint64_t tree_sum() const {
      if (std::holds_alternative<typename tree::Leaf>(this->v())) {
        return UINT64_C(0);
      } else {
        const auto &[a0, a1, a2] = std::get<typename tree::Node>(this->v());
        return ((a0->tree_sum() + a1) + a2->tree_sum());
      }
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, tree &, T1 &, uint64_t &, tree &,
                                     T1 &>
    T1 tree_rec(T1 f, F1 &&f0) const {
      if (std::holds_alternative<typename tree::Leaf>(this->v())) {
        return f;
      } else {
        const auto &[a0, a1, a2] = std::get<typename tree::Node>(this->v());
        return f0(*a0, a0->template tree_rec<T1>(f, f0), a1, *a2,
                  a2->template tree_rec<T1>(f, f0));
      }
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, tree &, T1 &, uint64_t &, tree &,
                                     T1 &>
    T1 tree_rect(T1 f, F1 &&f0) const {
      if (std::holds_alternative<typename tree::Leaf>(this->v())) {
        return f;
      } else {
        const auto &[a0, a1, a2] = std::get<typename tree::Node>(this->v());
        return f0(*a0, a0->template tree_rect<T1>(f, f0), a1, *a2,
                  a2->template tree_rect<T1>(f, f0));
      }
    }
  };

  /// test1: Create tree with sum=42, extract closures, apply to 0.
  /// Expected: 0 + 42 = 42, 42 + 20 = 62, 62 + 42 = 104.
  /// With dangling this, tree_sum reads garbage.
  static inline const uint64_t test1 = []() {
    fn_list fs =
        tree::node(tree::node(tree::leaf(), UINT64_C(10), tree::leaf()),
                   UINT64_C(20),
                   tree::node(tree::leaf(), UINT64_C(12), tree::leaf()))
            .extract_closures();
    return std::move(fs).apply_all(UINT64_C(0));
  }();
  /// test2: Allocate a noise tree between extracting closures and applying
  /// them. Increases memory pressure on freed region.
  static inline const uint64_t test2 = []() {
    fn_list fs = tree::node(tree::leaf(), UINT64_C(100), tree::leaf())
                     .extract_closures();
    uint64_t noise =
        tree::node(tree::leaf(), UINT64_C(999), tree::leaf()).tree_sum();
    return std::move(fs).apply_all(noise);
  }();
};

#endif // INCLUDED_ACCUM_CLOSURE_CAPTURE
