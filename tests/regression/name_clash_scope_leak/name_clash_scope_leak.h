#ifndef INCLUDED_NAME_CLASH_SCOPE_LEAK
#define INCLUDED_NAME_CLASH_SCOPE_LEAK

#include <memory>
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

  std::shared_ptr<List<t_A>> app(std::shared_ptr<List<t_A>> m) const {
    if (std::holds_alternative<typename List<t_A>::Nil>(this->v())) {
      return m;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<t_A>::Cons>(this->v());
      return List<t_A>::cons(d_a0, d_a1->app(m));
    }
  }
};

struct NameClashScopeLeak {
  /// Match on list, return list. Both branches produce the same type.
  static std::shared_ptr<List<unsigned int>>
  rotate(const std::shared_ptr<List<unsigned int>> &l);
  /// Two consecutive matches on different lists in the same function.
  __attribute__((pure)) static unsigned int
  heads_sum(const std::shared_ptr<List<unsigned int>> &l1,
            const std::shared_ptr<List<unsigned int>> &l2);
  /// Match on list, and in the Cons branch, match on the tail.
  __attribute__((pure)) static unsigned int
  first_two_sum(const std::shared_ptr<List<unsigned int>> &l);
  /// Match where both branches contain let bindings with same name.
  __attribute__((pure)) static unsigned int
  branch_let_clash(const std::shared_ptr<List<unsigned int>> &l);
  /// Three consecutive matches, each with same binding variable name pattern.
  __attribute__((pure)) static unsigned int
  triple_head(const std::shared_ptr<List<unsigned int>> &l1,
              const std::shared_ptr<List<unsigned int>> &l2,
              const std::shared_ptr<List<unsigned int>> &l3);
  /// Matching on a pair where both components are lists.
  __attribute__((pure)) static unsigned int
  pair_match(const std::pair<std::shared_ptr<List<unsigned int>>,
                             std::shared_ptr<List<unsigned int>>>
                 p);
};

#endif // INCLUDED_NAME_CLASH_SCOPE_LEAK
