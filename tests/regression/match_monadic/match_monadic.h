#ifndef INCLUDED_MATCH_MONADIC
#define INCLUDED_MATCH_MONADIC

#include <cstdint>
#include <filesystem>
#include <fstream>
#include <iostream>
#include <memory>
#include <optional>
#include <string>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

using namespace std::string_literals;
template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

/// A simple custom inductive for testing
enum class Color { e_RED, e_GREEN, e_BLUE }; /// A parameterized inductive

template <typename t_A> struct Tree {
  // TYPES
  struct Leaf {};

  struct Node {
    std::unique_ptr<Tree<t_A>> d_a0;
    t_A d_a1;
    std::unique_ptr<Tree<t_A>> d_a2;
  };

  using variant_t = std::variant<Leaf, Node>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  Tree() {}

  explicit Tree(Leaf _v) : d_v_(_v) {}

  explicit Tree(Node _v) : d_v_(std::move(_v)) {}

  Tree(const Tree<t_A> &_other) : d_v_(std::move(_other.clone().d_v_)) {}

  Tree(Tree<t_A> &&_other) : d_v_(std::move(_other.d_v_)) {}

  Tree<t_A> &operator=(const Tree<t_A> &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  Tree<t_A> &operator=(Tree<t_A> &&_other) {
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

    std::vector<_CloneFrame> _stack;
    _stack.push_back({this, &_out});
    while (!_stack.empty()) {
      auto _frame = _stack.back();
      _stack.pop_back();
      const Tree *_src = _frame._src;
      Tree *_dst = _frame._dst;
      if (std::holds_alternative<Leaf>(_src->v())) {
        const auto &_alt = std::get<Leaf>(_src->v());
        _dst->d_v_ = Leaf{};
      } else {
        const auto &_alt = std::get<Node>(_src->v());
        _dst->d_v_ =
            Node{_alt.d_a0 ? std::make_unique<Tree>() : nullptr, _alt.d_a1,
                 _alt.d_a2 ? std::make_unique<Tree>() : nullptr};
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
  template <typename _U> explicit Tree(const Tree<_U> &_other) {
    if (std::holds_alternative<typename Tree<_U>::Leaf>(_other.v())) {
      d_v_ = Leaf{};
    } else {
      const auto &[d_a0, d_a1, d_a2] =
          std::get<typename Tree<_U>::Node>(_other.v());
      d_v_ =
          Node{d_a0 ? std::make_unique<Tree<t_A>>(*d_a0) : nullptr, t_A(d_a1),
               d_a2 ? std::make_unique<Tree<t_A>>(*d_a2) : nullptr};
    }
  }

  static Tree<t_A> leaf() { return Tree(Leaf{}); }

  static Tree<t_A> node(Tree<t_A> a0, t_A a1, Tree<t_A> a2) {
    return Tree(Node{std::make_unique<Tree<t_A>>(std::move(a0)), std::move(a1),
                     std::make_unique<Tree<t_A>>(std::move(a2))});
  }

  // MANIPULATORS
  ~Tree() {
    std::vector<std::unique_ptr<Tree>> _stack;
    auto _drain = [&](Tree &_node) {
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
};

struct MatchMonadic {
  /// 1. Match on custom inductive with effects in each arm
  static std::string color_name(const Color c);
  /// 2. Match on bool inside a bind chain
  static std::string conditional_read(const bool &b);
  /// 3. Nested match: match on result of another match
  static std::string nested_match(const unsigned int &n, const bool &b);
  /// 4. Match on option in monadic context
  static unsigned int handle_option(const std::optional<unsigned int> &o);
  /// 5. Recursive function matching on tree
  static unsigned int tree_sum(const Tree<unsigned int> &t);
  /// 6. Match result used in bind
  static std::string match_then_bind(const unsigned int &n);
  /// 7. Match inside a bind continuation
  static int64_t bind_then_match();
  /// 8. Multiple matches in sequence
  static std::string multi_match(const bool &a, const bool &b);
};

#endif // INCLUDED_MATCH_MONADIC
