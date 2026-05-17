#ifndef INCLUDED_VISIT_MATCH_BUG
#define INCLUDED_VISIT_MATCH_BUG

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

struct VisitMatchBug {
  struct Tree {
    // TYPES
    struct Leaf {
      uint64_t a0;
    };

    struct Node {
      std::unique_ptr<Tree> a0;
      uint64_t a1;
      std::unique_ptr<Tree> a2;
    };

    using variant_t = std::variant<Leaf, Node>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    Tree() {}

    explicit Tree(Leaf _v) : v_(std::move(_v)) {}

    explicit Tree(Node _v) : v_(std::move(_v)) {}

    Tree(const Tree &_other) : v_(std::move(_other.clone().v_)) {}

    Tree(Tree &&_other) noexcept : v_(std::move(_other.v_)) {}

    Tree &operator=(const Tree &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    Tree &operator=(Tree &&_other) noexcept {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    Tree clone() const {
      Tree _out{};

      struct _CloneFrame {
        const Tree *_src;
        Tree *_dst;
      };

      std::vector<_CloneFrame> _stack{};
      _stack.reserve(8);
      _stack.push_back({this, &_out});
      while (!_stack.empty()) {
        auto _frame = _stack.back();
        _stack.pop_back();
        const Tree *_src = _frame._src;
        Tree *_dst = _frame._dst;
        if (std::holds_alternative<Leaf>(_src->v())) {
          const auto &_alt = std::get<Leaf>(_src->v());
          _dst->v_ = Leaf{_alt.a0};
        } else {
          const auto &_alt = std::get<Node>(_src->v());
          _dst->v_ = Node{_alt.a0 ? std::make_unique<Tree>() : nullptr, _alt.a1,
                          _alt.a2 ? std::make_unique<Tree>() : nullptr};
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
    static Tree leaf(uint64_t a0) { return Tree(Leaf{a0}); }

    static Tree node(Tree a0, uint64_t a1, Tree a2) {
      return Tree(Node{std::make_unique<Tree>(std::move(a0)), a1,
                       std::make_unique<Tree>(std::move(a2))});
    }

    // MANIPULATORS
    ~Tree() {
      std::vector<std::unique_ptr<Tree>> _stack{};
      _stack.reserve(8);
      auto _drain = [&](Tree &_node) {
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
  };

  template <typename T1, typename F0, typename F1>
    requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
             std::is_invocable_r_v<T1, F1 &, Tree &, T1 &, uint64_t &, Tree &,
                                   T1 &>
  static T1 Tree_rect(F0 &&f, F1 &&f0, const Tree &t) {
    if (std::holds_alternative<typename Tree::Leaf>(t.v())) {
      const auto &[a0] = std::get<typename Tree::Leaf>(t.v());
      return f(a0);
    } else {
      const auto &[a0, a1, a2] = std::get<typename Tree::Node>(t.v());
      return f0(*a0, Tree_rect<T1>(f, f0, *a0), a1, *a2,
                Tree_rect<T1>(f, f0, *a2));
    }
  }

  template <typename T1, typename F0, typename F1>
    requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
             std::is_invocable_r_v<T1, F1 &, Tree &, T1 &, uint64_t &, Tree &,
                                   T1 &>
  static T1 Tree_rec(F0 &&f, F1 &&f0, const Tree &t) {
    if (std::holds_alternative<typename Tree::Leaf>(t.v())) {
      const auto &[a0] = std::get<typename Tree::Leaf>(t.v());
      return f(a0);
    } else {
      const auto &[a0, a1, a2] = std::get<typename Tree::Node>(t.v());
      return f0(*a0, Tree_rec<T1>(f, f0, *a0), a1, *a2,
                Tree_rec<T1>(f, f0, *a2));
    }
  }

  static Tree consume(Tree t);
  static uint64_t match_after_consume(const Tree &t);
  static uint64_t match_last_use(const Tree &t);
  static uint64_t nested_match_consume(const Tree &t);
  static uint64_t chain_then_match(const Tree &t1);

  struct State {
    uint64_t value;
    uint64_t data;

    // ACCESSORS
    State clone() const { return State{(*this).value, (*this).data}; }
  };

  static uint64_t match_extract_field(const State &s);
  static uint64_t match_extract_two(const State &s);
  static uint64_t match_nested(const State &s);
  static uint64_t match_in_tail(const State &s);
  static uint64_t match_in_expr(const State &s);
};

#endif // INCLUDED_VISIT_MATCH_BUG
