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
concept MapsTo = std::is_invocable_v<F &, Args &...>;

template <typename T> struct is_unique_ptr : std::false_type {};

template <typename T>
struct is_unique_ptr<std::unique_ptr<T>> : std::true_type {
  using element_type = T;
};

template <typename T> auto clone_value(const T &x) { return x; }

template <typename T>
std::unique_ptr<T> clone_value(const std::unique_ptr<T> &x) {
  if constexpr (requires { x->clone(); }) {
    return x ? std::make_unique<T>(x->clone()) : nullptr;
  } else {
    return x ? std::make_unique<T>(*x) : nullptr;
  }
}

template <typename Target, typename Source>
Target clone_as_value(const Source &x) {
  using T = std::remove_cvref_t<Target>;
  using S = std::remove_cvref_t<Source>;
  if constexpr (requires(const S &s) {
                  s.has_value();
                  *s;
                }) {
    if (!x.has_value())
      return T{};
    using TInner = std::remove_cvref_t<decltype(*std::declval<const T &>())>;
    return T{clone_as_value<TInner>(*x)};
  } else if constexpr (std::is_same_v<T, S>) {
    if constexpr (is_unique_ptr<T>::value) {
      return clone_value(x);
    } else if constexpr (requires { x.clone(); }) {
      return x.clone();
    } else {
      return x;
    }
  } else if constexpr (is_unique_ptr<S>::value) {
    if (!x)
      return T{};
    return clone_as_value<T>(*x);
  } else if constexpr (is_unique_ptr<T>::value) {
    using Inner = typename is_unique_ptr<T>::element_type;
    return std::make_unique<Inner>(clone_as_value<Inner>(x));
  } else {
    return T(x);
  }
}

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
  using crane_element_type = t_A;

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

  __attribute__((pure)) Tree<t_A> &operator=(const Tree<t_A> &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  __attribute__((pure)) Tree<t_A> &operator=(Tree<t_A> &&_other) {
    d_v_ = std::move(_other.d_v_);
    return *this;
  }

  // ACCESSORS
  __attribute__((pure)) Tree<t_A> clone() const {
    auto &&_sv = *(this);
    if (std::holds_alternative<Leaf>(_sv.v())) {
      return Tree<t_A>(Leaf{});
    } else {
      const auto &[d_a0, d_a1, d_a2] = std::get<Node>(_sv.v());
      return Tree<t_A>(
          Node{clone_value(d_a0), clone_value(d_a1), clone_value(d_a2)});
    }
  }

  // CREATORS
  template <typename _U> explicit Tree(const Tree<_U> &_other) {
    if (std::holds_alternative<typename Tree<_U>::Leaf>(_other.v())) {
      d_v_ = Leaf{};
    } else {
      const auto &[d_a0, d_a1, d_a2] =
          std::get<typename Tree<_U>::Node>(_other.v());
      d_v_ = Node{d_a0 ? std::make_unique<Tree<t_A>>(*d_a0) : nullptr,
                  clone_as_value<t_A>(d_a1),
                  d_a2 ? std::make_unique<Tree<t_A>>(*d_a2) : nullptr};
    }
  }

  __attribute__((pure)) static Tree<t_A> leaf() { return Tree(Leaf{}); }

  __attribute__((pure)) static Tree<t_A> node(const Tree<t_A> &a0, t_A a1,
                                              const Tree<t_A> &a2) {
    return Tree(Node{std::make_unique<Tree<t_A>>(a0), std::move(a1),
                     std::make_unique<Tree<t_A>>(a2)});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) Tree<t_A> *operator->() { return this; }

  __attribute__((pure)) const Tree<t_A> *operator->() const { return this; }

  __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

  __attribute__((pure)) bool operator==(std::nullptr_t) const { return false; }

  // MANIPULATORS
  void reset() { *this = Tree<t_A>(); }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
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
