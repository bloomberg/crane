#ifndef INCLUDED_LIST_CLOSURE_ESCAPE
#define INCLUDED_LIST_CLOSURE_ESCAPE

#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

struct ListClosureEscape {
  struct tree {
    // TYPES
    struct Leaf {};

    struct Node {
      std::unique_ptr<tree> a0;
      unsigned int a1;
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

    static tree node(tree a0, unsigned int a1, tree a2) {
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

    unsigned int sum_values(unsigned int x) const {
      if (std::holds_alternative<typename tree::Leaf>(this->v())) {
        return x;
      } else {
        const auto &[a0, a1, a2] = std::get<typename tree::Node>(this->v());
        auto &&_sv0 = *a0;
        if (std::holds_alternative<typename tree::Leaf>(_sv0.v())) {
          return (a1 + x);
        } else {
          const auto &[a00, a10, a20] = std::get<typename tree::Node>(_sv0.v());
          auto &&_sv1 = *a2;
          if (std::holds_alternative<typename tree::Leaf>(_sv1.v())) {
            return (a10 + x);
          } else {
            const auto &[a01, a11, a21] =
                std::get<typename tree::Node>(_sv1.v());
            return (((a10 + a11) + a1) + x);
          }
        }
      }
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, tree &, T1 &, unsigned int &,
                                     tree &, T1 &>
    T1 tree_rec(T1 f, F1 &&f0) const {
      if (std::holds_alternative<typename tree::Leaf>(this->v())) {
        return f;
      } else {
        const auto &[a0, a1, a2] = std::get<typename tree::Node>(this->v());
        return f0(*a0, (*a0).template tree_rec<T1>(f, f0), a1, *a2,
                  (*a2).template tree_rec<T1>(f, f0));
      }
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, tree &, T1 &, unsigned int &,
                                     tree &, T1 &>
    T1 tree_rect(T1 f, F1 &&f0) const {
      if (std::holds_alternative<typename tree::Leaf>(this->v())) {
        return f;
      } else {
        const auto &[a0, a1, a2] = std::get<typename tree::Node>(this->v());
        return f0(*a0, (*a0).template tree_rect<T1>(f, f0), a1, *a2,
                  (*a2).template tree_rect<T1>(f, f0));
      }
    }
  };

  /// A simple list of closures.
  struct fn_list {
    // TYPES
    struct FNil {};

    struct FCons {
      std::function<unsigned int(unsigned int)> a0;
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

    static fn_list fcons(std::function<unsigned int(unsigned int)> a0,
                         fn_list a1) {
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

    unsigned int apply_first(unsigned int x) const {
      if (std::holds_alternative<typename fn_list::FNil>(this->v())) {
        return x;
      } else {
        const auto &[a0, a1] = std::get<typename fn_list::FCons>(this->v());
        return a0(x);
      }
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<
          T1, F1 &, std::function<unsigned int(unsigned int)> &, fn_list &,
          T1 &>
    T1 fn_list_rec(T1 f, F1 &&f0) const {
      if (std::holds_alternative<typename fn_list::FNil>(this->v())) {
        return f;
      } else {
        const auto &[a0, a1] = std::get<typename fn_list::FCons>(this->v());
        return f0(a0, *a1, (*a1).template fn_list_rec<T1>(f, f0));
      }
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<
          T1, F1 &, std::function<unsigned int(unsigned int)> &, fn_list &,
          T1 &>
    T1 fn_list_rect(T1 f, F1 &&f0) const {
      if (std::holds_alternative<typename fn_list::FNil>(this->v())) {
        return f;
      } else {
        const auto &[a0, a1] = std::get<typename fn_list::FCons>(this->v());
        return f0(a0, *a1, (*a1).template fn_list_rect<T1>(f, f0));
      }
    }
  };

  /// BUG: partial applications stored in a custom list via FCons.
  /// Each lambda for (sum_values t_i) captures t_i by &.
  /// When build_fns returns, t1 and t2 are destroyed.
  static fn_list build_fns(tree t1, tree t2);
  static inline const unsigned int bug_list_clobber = []() {
    tree t1 = tree::node(tree::node(tree::leaf(), 10u, tree::leaf()), 20u,
                         tree::node(tree::leaf(), 30u, tree::leaf()));
    tree t2 = tree::node(tree::node(tree::leaf(), 77u, tree::leaf()), 88u,
                         tree::node(tree::leaf(), 99u, tree::leaf()));
    fn_list fns = build_fns(std::move(t1), std::move(t2));
    return std::move(fns).apply_first(0u);
  }();
};

#endif // INCLUDED_LIST_CLOSURE_ESCAPE
