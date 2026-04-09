#ifndef INCLUDED_LET_MATCH_TYPE2
#define INCLUDED_LET_MATCH_TYPE2

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

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
  explicit List(Nil _v) : d_v_(std::move(_v)) {}

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

struct LetMatchType2 {
  /// 1. Match returning bool — should be fine
  __attribute__((pure)) static bool let_match_bool(const unsigned int n);
  /// 2. Match returning pair — might trigger std::any
  __attribute__((pure)) static unsigned int let_match_pair(const bool b);
  /// 3. Match returning list — might trigger std::any
  static std::shared_ptr<List<unsigned int>> let_match_list(const bool b);
  /// 4. Match returning option — might trigger std::any
  __attribute__((pure)) static std::optional<unsigned int>
  let_match_opt(const bool b);
  /// 5. Cascading let-matches all returning nat — should be fine
  __attribute__((pure)) static unsigned int
  cascading_nat(const bool a, const bool b, const bool c);
  /// 6. Match returning function type
  __attribute__((pure)) static unsigned int let_match_fun(const bool b);
  /// 7. Match result used in another match
  __attribute__((pure)) static unsigned int
  match_of_match(const unsigned int n);

  /// 8. let-bound match where arms have bindings
  __attribute__((pure)) static unsigned int
  let_match_bindings(const unsigned int n);
};

#endif // INCLUDED_LET_MATCH_TYPE2
