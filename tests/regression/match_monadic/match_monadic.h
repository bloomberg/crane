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

using namespace std::string_literals;
template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

/// A simple custom inductive for testing
enum class Color { e_RED, e_GREEN, e_BLUE }; /// A parameterized inductive

template <typename t_A> struct Tree {
  // TYPES
  struct Leaf {};

  struct Node {
    std::shared_ptr<Tree<t_A>> d_a0;
    t_A d_a1;
    std::shared_ptr<Tree<t_A>> d_a2;
  };

  using variant_t = std::variant<Leaf, Node>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  explicit Tree(Leaf _v) : d_v_(std::move(_v)) {}

  explicit Tree(Node _v) : d_v_(std::move(_v)) {}

  static std::shared_ptr<Tree<t_A>> leaf() {
    return std::make_shared<Tree<t_A>>(Leaf{});
  }

  static std::shared_ptr<Tree<t_A>> node(const std::shared_ptr<Tree<t_A>> &a0,
                                         t_A a1,
                                         const std::shared_ptr<Tree<t_A>> &a2) {
    return std::make_shared<Tree<t_A>>(Node{a0, std::move(a1), a2});
  }

  static std::shared_ptr<Tree<t_A>> node(std::shared_ptr<Tree<t_A>> &&a0,
                                         t_A a1,
                                         std::shared_ptr<Tree<t_A>> &&a2) {
    return std::make_shared<Tree<t_A>>(
        Node{std::move(a0), std::move(a1), std::move(a2)});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
};

struct MatchMonadic {
  /// 1. Match on custom inductive with effects in each arm
  static std::string color_name(const Color c);
  /// 2. Match on bool inside a bind chain
  static std::string conditional_read(const bool b);
  /// 3. Nested match: match on result of another match
  static std::string nested_match(const unsigned int n, const bool b);
  /// 4. Match on option in monadic context
  static unsigned int handle_option(const std::optional<unsigned int> o);
  /// 5. Recursive function matching on tree
  static unsigned int tree_sum(const std::shared_ptr<Tree<unsigned int>> &t);
  /// 6. Match result used in bind
  static std::string match_then_bind(const unsigned int n);
  /// 7. Match inside a bind continuation
  static int64_t bind_then_match();
  /// 8. Multiple matches in sequence
  static std::string multi_match(const bool a, const bool b);
};

#endif // INCLUDED_MATCH_MONADIC
