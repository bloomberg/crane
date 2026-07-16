#ifndef INCLUDED_MATCH_MONADIC
#define INCLUDED_MATCH_MONADIC

#include <any>
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
enum class Color { RED, GREEN, BLUE };

/// A parameterized inductive
template <typename A> struct Tree {
  // TYPES
  struct Leaf {};

  struct Node {
    std::shared_ptr<Tree<A>> a0;
    A a1;
    std::shared_ptr<Tree<A>> a2;
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

  template <typename _U> explicit Tree(const Tree<_U> &_other) {
    if (std::holds_alternative<typename Tree<_U>::Leaf>(_other.v())) {
      this->v_ = Leaf{};
    } else {
      const auto &[a0, a1, a2] = std::get<typename Tree<_U>::Node>(_other.v());
      this->v_ = Node{
          a0 ? std::make_shared<Tree<A>>(*a0) : nullptr,
          [&]() -> A {
            if constexpr (std::is_same_v<_U, std::any>) {
              if (a1.type() == typeid(A))
                return std::any_cast<A>(a1);
              if constexpr (requires {
                              typename A::first_type;
                              typename A::second_type;
                            }) {
                const auto &[_k, _v] =
                    std::any_cast<std::pair<std::any, std::any>>(a1);
                return A{[&]() -> typename A::first_type {
                           if constexpr (std::is_same_v<typename A::first_type,
                                                        std::any>)
                             return _k;
                           else
                             return std::any_cast<typename A::first_type>(_k);
                         }(),
                         [&]() -> typename A::second_type {
                           if constexpr (std::is_same_v<typename A::second_type,
                                                        std::any>)
                             return _v;
                           else
                             return std::any_cast<typename A::second_type>(_v);
                         }()};
              }
              return std::any_cast<A>(a1);
            } else
              return A(a1);
          }(),
          a2 ? std::make_shared<Tree<A>>(*a2) : nullptr};
    }
  }

  static Tree<A> leaf() { return Tree(Leaf{}); }

  static Tree<A> node(Tree<A> a0, A a1, Tree<A> a2) {
    return Tree(Node{std::make_shared<Tree<A>>(std::move(a0)), std::move(a1),
                     std::make_shared<Tree<A>>(std::move(a2))});
  }

  // MANIPULATORS
  ~Tree() {
    std::vector<std::shared_ptr<Tree<A>>> _stack = {};
    auto _drain = [&](variant_t &_v) {
      if (auto *_alt = std::get_if<Node>(&_v)) {
        if (_alt->a0) {
          _stack.push_back(std::move(_alt->a0));
        }
        if (_alt->a2) {
          _stack.push_back(std::move(_alt->a2));
        }
      }
    };
    _drain(v_mut());
    while (!_stack.empty()) {
      auto _cur = std::move(_stack.back());
      _stack.pop_back();
      if (_cur.use_count() == 1) {
        _drain(_cur->v_mut());
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
  static std::string nested_match(uint64_t n, bool b);
  /// 4. Match on option in monadic context
  static uint64_t handle_option(const std::optional<uint64_t> &o);
  /// 5. Recursive function matching on tree
  static uint64_t tree_sum(const Tree<uint64_t> &t);
  /// 6. Match result used in bind
  static std::string match_then_bind(uint64_t n);
  /// 7. Match inside a bind continuation
  static int64_t bind_then_match();
  /// 8. Multiple matches in sequence
  static std::string multi_match(bool a, bool b);
};

#endif // INCLUDED_MATCH_MONADIC
