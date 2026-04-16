#ifndef INCLUDED_CUSTOM_INLINE_BUG
#define INCLUDED_CUSTOM_INLINE_BUG

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <typename t_A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    t_A d_a0;
    std::shared_ptr<List<t_A>> d_a1;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  explicit List(Nil _v) : d_v_(_v) {}

  explicit List(Cons _v) : d_v_(std::move(_v)) {}

  static std::shared_ptr<List<t_A>> nil() {
    return std::make_shared<List<t_A>>(Nil{});
  }

  static std::shared_ptr<List<t_A>> cons(t_A a0,
                                         const std::shared_ptr<List<t_A>> &a1) {
    return std::make_shared<List<t_A>>(Cons{std::move(a0), a1});
  }

  static std::shared_ptr<List<t_A>> cons(t_A a0,
                                         std::shared_ptr<List<t_A>> &&a1) {
    return std::make_shared<List<t_A>>(Cons{std::move(a0), std::move(a1)});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
};

struct CustomInlineBug {
  struct State {
    unsigned int value;
    unsigned int data;
  };

  __attribute__((pure)) static std::optional<unsigned int>
  bug_some_proj(const std::shared_ptr<State> &s);
  __attribute__((pure)) static std::pair<std::shared_ptr<State>, unsigned int>
  bug_pair_proj(std::shared_ptr<State> s);
  __attribute__((pure)) static std::optional<std::optional<unsigned int>>
  bug_nested_option(const std::shared_ptr<State> &s);
  __attribute__((pure)) static std::optional<
      std::pair<std::shared_ptr<State>, unsigned int>>
  bug_option_pair(std::shared_ptr<State> s);
  static std::shared_ptr<State> get_state(const unsigned int n);
  __attribute__((pure)) static std::optional<unsigned int>
  bug_some_of_call(const unsigned int n);
  __attribute__((pure)) static std::pair<std::shared_ptr<State>, unsigned int>
  pair_simple(std::shared_ptr<State> s);
  __attribute__((pure)) static std::pair<std::shared_ptr<State>, unsigned int>
  pair_let(const unsigned int n);
  __attribute__((
      pure)) static std::pair<std::pair<std::shared_ptr<State>, unsigned int>,
                              std::pair<unsigned int, unsigned int>>
  pair_nested(std::shared_ptr<State> s);
  __attribute__((pure)) static std::pair<std::shared_ptr<State>, unsigned int>
  pair_if(const bool b, std::shared_ptr<State> s);
  __attribute__((pure)) static std::optional<
      std::pair<std::shared_ptr<State>, unsigned int>>
  pair_match(const std::optional<std::shared_ptr<State>> o);
  __attribute__((pure)) static std::pair<
      std::pair<std::shared_ptr<State>, unsigned int>, unsigned int>
  pair_multi_proj(std::shared_ptr<State> s);
  __attribute__((pure)) static std::pair<std::shared_ptr<State>, unsigned int>
  pair_chain(const std::shared_ptr<State> &s1);
  __attribute__((pure)) static std::pair<
      std::pair<std::shared_ptr<State>, std::shared_ptr<State>>,
      std::pair<unsigned int, unsigned int>>
  pair_extreme(std::shared_ptr<State> s);
  __attribute__((pure)) static std::pair<std::shared_ptr<State>, unsigned int>
  make_pair(std::shared_ptr<State> s);
  __attribute__((pure)) static std::pair<std::shared_ptr<State>, unsigned int>
  outer_pair(const unsigned int n);
  static std::shared_ptr<List<std::pair<std::shared_ptr<State>, unsigned int>>>
  count_pairs(const unsigned int n, std::shared_ptr<State> s);
};

#endif // INCLUDED_CUSTOM_INLINE_BUG
