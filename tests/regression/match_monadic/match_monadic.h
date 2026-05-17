#ifndef INCLUDED_MATCH_MONADIC
#define INCLUDED_MATCH_MONADIC

#include <cstdint>
#include <filesystem>
#include <fstream>
#include <iostream>
#include <memory>
#include <optional>
#include <string>
#include <utility>
#include <variant>
#include <vector>

using namespace std::string_literals;

/// A simple custom inductive for testing
enum class Color { RED, GREEN, BLUE }; /// A parameterized inductive

template <typename A> struct Tree {
  // TYPES
  struct Leaf {};

  struct Node {
    std::unique_ptr<Tree<A>> a0;
    A a1;
    std::unique_ptr<Tree<A>> a2;
  };

  using variant_t = std::variant<Leaf, Node>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Tree() {}

  explicit Tree(Leaf _v) : v_(_v) {}

  explicit Tree(Node _v) : v_(std::move(_v)) {}

  Tree(const Tree<A> &_other) : v_(std::move(_other.clone().v_)) {}

  Tree(Tree<A> &&_other) noexcept : v_(std::move(_other.v_)) {}

  Tree<A> &operator=(const Tree<A> &_other) {
    v_ = std::move(_other.clone().v_);
    return *this;
  }

  Tree<A> &operator=(Tree<A> &&_other) noexcept {
    v_ = std::move(_other.v_);
    return *this;
  }

  // ACCESSORS
  Tree<A> clone() const {
    Tree<A> _out{};

    struct _CloneFrame {
      const Tree<A> *_src;
      Tree<A> *_dst;
    };

    std::vector<_CloneFrame> _stack{};
    _stack.reserve(8);
    _stack.push_back({this, &_out});
    while (!_stack.empty()) {
      auto _frame = _stack.back();
      _stack.pop_back();
      const Tree<A> *_src = _frame._src;
      Tree<A> *_dst = _frame._dst;
      if (std::holds_alternative<Leaf>(_src->v())) {
        _dst->v_ = Leaf{};
      } else {
        const auto &_alt = std::get<Node>(_src->v());
        _dst->v_ =
            Node{_alt.a0 ? std::make_unique<Tree<A>>() : nullptr, _alt.a1,
                 _alt.a2 ? std::make_unique<Tree<A>>() : nullptr};
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
  template <typename _U> explicit Tree(const Tree<_U> &_other) {
    if (std::holds_alternative<typename Tree<_U>::Leaf>(_other.v())) {
      this->v_ = Leaf{};
    } else {
      const auto &[a0, a1, a2] = std::get<typename Tree<_U>::Node>(_other.v());
      this->v_ = Node{a0 ? std::make_unique<Tree<A>>(*a0) : nullptr, A(a1),
                      a2 ? std::make_unique<Tree<A>>(*a2) : nullptr};
    }
  }

  static Tree<A> leaf() { return Tree(Leaf{}); }

  static Tree<A> node(Tree<A> a0, A a1, Tree<A> a2) {
    return Tree(Node{std::make_unique<Tree<A>>(std::move(a0)), std::move(a1),
                     std::make_unique<Tree<A>>(std::move(a2))});
  }

  // MANIPULATORS
  ~Tree() {
    std::vector<std::unique_ptr<Tree<A>>> _stack{};
    _stack.reserve(8);
    auto _drain = [&](Tree<A> &_node) {
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

struct MatchMonadic {
  /// 1. Match on custom inductive with effects in each arm
  static std::string color_name(Color c);
  /// 2. Match on bool inside a bind chain
  static std::string conditional_read(bool b);
  /// 3. Nested match: match on result of another match
  static std::string nested_match(unsigned int n, bool b);
  /// 4. Match on option in monadic context
  static unsigned int handle_option(const std::optional<unsigned int> &o);
  /// 5. Recursive function matching on tree
  static unsigned int tree_sum(const Tree<unsigned int> &t);
  /// 6. Match result used in bind
  static std::string match_then_bind(unsigned int n);
  /// 7. Match inside a bind continuation
  static int64_t bind_then_match();
  /// 8. Multiple matches in sequence
  static std::string multi_match(bool a, bool b);
};

#endif // INCLUDED_MATCH_MONADIC
