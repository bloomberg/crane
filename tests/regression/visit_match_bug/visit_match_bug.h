#ifndef INCLUDED_VISIT_MATCH_BUG
#define INCLUDED_VISIT_MATCH_BUG

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

struct VisitMatchBug {
  struct Tree {
    // TYPES
    struct Leaf {
      unsigned int d_a0;
    };

    struct Node {
      std::unique_ptr<Tree> d_a0;
      unsigned int d_a1;
      std::unique_ptr<Tree> d_a2;
    };

    using variant_t = std::variant<Leaf, Node>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    Tree() {}

    explicit Tree(Leaf _v) : d_v_(std::move(_v)) {}

    explicit Tree(Node _v) : d_v_(std::move(_v)) {}

    Tree(const Tree &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    Tree(Tree &&_other) : d_v_(std::move(_other.d_v_)) {}

    Tree &operator=(const Tree &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    Tree &operator=(Tree &&_other) {
      d_v_ = std::move(_other.d_v_);
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
      _stack.push_back({this, &_out});
      while (!_stack.empty()) {
        auto _frame = _stack.back();
        _stack.pop_back();
        const Tree *_src = _frame._src;
        Tree *_dst = _frame._dst;
        if (std::holds_alternative<Leaf>(_src->v())) {
          const auto &_alt = std::get<Leaf>(_src->v());
          _dst->d_v_ = Leaf{_alt.d_a0};
        } else {
          const auto &_alt = std::get<Node>(_src->v());
          _dst->d_v_ =
              Node{_alt.d_a0 ? std::make_unique<Tree>() : nullptr, _alt.d_a1,
                   _alt.d_a2 ? std::make_unique<Tree>() : nullptr};
          auto &_dst_alt = std::get<Node>(_dst->d_v_);
          if (_alt.d_a0) {
            _stack.push_back({_alt.d_a0.get(), _dst_alt.d_a0.get()});
          }
          if (_alt.d_a2) {
            _stack.push_back({_alt.d_a2.get(), _dst_alt.d_a2.get()});
          }
        }
      }
      return _out;
    }

    // CREATORS
    static Tree leaf(unsigned int a0) { return Tree(Leaf{std::move(a0)}); }

    static Tree node(Tree a0, unsigned int a1, Tree a2) {
      return Tree(Node{std::make_unique<Tree>(std::move(a0)), std::move(a1),
                       std::make_unique<Tree>(std::move(a2))});
    }

    // MANIPULATORS
    ~Tree() {
      std::vector<std::unique_ptr<Tree>> _stack{};
      auto _drain = [&](Tree &_node) {
        if (std::holds_alternative<Node>(_node.d_v_)) {
          auto &_alt = std::get<Node>(_node.d_v_);
          if (_alt.d_a0) {
            _stack.push_back(std::move(_alt.d_a0));
          }
          if (_alt.d_a2) {
            _stack.push_back(std::move(_alt.d_a2));
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

    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, unsigned int> F0,
            MapsTo<T1, Tree, T1, unsigned int, Tree, T1> F1>
  static T1 Tree_rect(F0 &&f, F1 &&f0, const Tree &t) {
    if (std::holds_alternative<typename Tree::Leaf>(t.v())) {
      const auto &[d_a0] = std::get<typename Tree::Leaf>(t.v());
      return f(d_a0);
    } else {
      const auto &[d_a0, d_a1, d_a2] = std::get<typename Tree::Node>(t.v());
      return f0(*(d_a0), Tree_rect<T1>(f, f0, *(d_a0)), d_a1, *(d_a2),
                Tree_rect<T1>(f, f0, *(d_a2)));
    }
  }

  template <typename T1, MapsTo<T1, unsigned int> F0,
            MapsTo<T1, Tree, T1, unsigned int, Tree, T1> F1>
  static T1 Tree_rec(F0 &&f, F1 &&f0, const Tree &t) {
    if (std::holds_alternative<typename Tree::Leaf>(t.v())) {
      const auto &[d_a0] = std::get<typename Tree::Leaf>(t.v());
      return f(d_a0);
    } else {
      const auto &[d_a0, d_a1, d_a2] = std::get<typename Tree::Node>(t.v());
      return f0(*(d_a0), Tree_rec<T1>(f, f0, *(d_a0)), d_a1, *(d_a2),
                Tree_rec<T1>(f, f0, *(d_a2)));
    }
  }

  static Tree consume(Tree t);
  static unsigned int match_after_consume(const Tree &t);
  static unsigned int match_last_use(const Tree &t);
  static unsigned int nested_match_consume(const Tree &t);
  static unsigned int chain_then_match(const Tree &t1);

  struct State {
    unsigned int value;
    unsigned int data;

    // ACCESSORS
    State clone() const { return State{(*(this)).value, (*(this)).data}; }
  };

  static unsigned int match_extract_field(const State &s);
  static unsigned int match_extract_two(const State &s);
  static unsigned int match_nested(const State &s);
  static unsigned int match_in_tail(const State &s);
  static unsigned int match_in_expr(const State &s);
};

#endif // INCLUDED_VISIT_MATCH_BUG
