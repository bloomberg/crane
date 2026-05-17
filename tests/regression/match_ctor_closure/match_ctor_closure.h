#ifndef INCLUDED_MATCH_CTOR_CLOSURE
#define INCLUDED_MATCH_CTOR_CLOSURE

#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

struct MatchCtorClosure {
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

    uint64_t sum_values(uint64_t x) const {
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
      requires std::is_invocable_r_v<T1, F1 &, tree &, T1 &, uint64_t &, tree &,
                                     T1 &>
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
      requires std::is_invocable_r_v<T1, F1 &, tree &, T1 &, uint64_t &, tree &,
                                     T1 &>
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

  struct fn_box {
    // DATA
    std::function<uint64_t(uint64_t)> a0;

    // ACCESSORS
    fn_box clone() const { return {a0}; }

    // CREATORS
    static fn_box box(std::function<uint64_t(uint64_t)> a0) {
      return {std::move(a0)};
    }

    uint64_t apply_box(uint64_t x) const {
      const auto &_sv = *this;
      const auto &[a0] = _sv;
      return a0(x);
    }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &,
                                     std::function<uint64_t(uint64_t)> &>
    T1 fn_box_rec(F0 &&f) const {
      const auto &_sv = *this;
      const auto &[a0] = _sv;
      return f(a0);
    }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &,
                                     std::function<uint64_t(uint64_t)> &>
    T1 fn_box_rect(F0 &&f) const {
      const auto &_sv = *this;
      const auto &[a0] = _sv;
      return f(a0);
    }
  };

  /// BUG HYPOTHESIS: Match arm stores a partial application (closure)
  /// in a constructor. The lambda captures a PATTERN VARIABLE (_args.d_a0)
  /// by & reference. When the visit lambda returns, _args is destroyed
  /// but the fn_box retains the closure with a dangling reference.
  static fn_box match_and_box(const tree &t);
  /// Clobber stack, then use the closure from the box.
  static inline const uint64_t bug_match_ctor = []() {
    tree t = tree::node(tree::node(tree::leaf(), UINT64_C(10), tree::leaf()),
                        UINT64_C(20),
                        tree::node(tree::leaf(), UINT64_C(30), tree::leaf()));
    fn_box b = match_and_box(std::move(t));
    return std::move(b).apply_box(UINT64_C(5));
  }();
};

#endif // INCLUDED_MATCH_CTOR_CLOSURE
