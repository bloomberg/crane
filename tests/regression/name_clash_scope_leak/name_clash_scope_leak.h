#ifndef INCLUDED_NAME_CLASH_SCOPE_LEAK
#define INCLUDED_NAME_CLASH_SCOPE_LEAK

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

template <typename t_A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    t_A d_a0;
    std::unique_ptr<List<t_A>> d_a1;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  List() {}

  explicit List(Nil _v) : d_v_(_v) {}

  explicit List(Cons _v) : d_v_(std::move(_v)) {}

  List(const List<t_A> &_other) : d_v_(std::move(_other.clone().d_v_)) {}

  List(List<t_A> &&_other) : d_v_(std::move(_other.d_v_)) {}

  List<t_A> &operator=(const List<t_A> &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  List<t_A> &operator=(List<t_A> &&_other) {
    d_v_ = std::move(_other.d_v_);
    return *this;
  }

  // ACCESSORS
  __attribute__((pure)) List<t_A> clone() const {
    auto &&_sv = *(this);
    if (std::holds_alternative<Nil>(_sv.v())) {
      return List<t_A>(Nil{});
    } else {
      const auto &[d_a0, d_a1] = std::get<Cons>(_sv.v());
      return List<t_A>(Cons{
          d_a0, d_a1 ? std::make_unique<List<t_A>>(d_a1->clone()) : nullptr});
    }
  }

  // CREATORS
  template <typename _U> explicit List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      d_v_ = Nil{};
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<_U>::Cons>(_other.v());
      d_v_ =
          Cons{t_A(d_a0), d_a1 ? std::make_unique<List<t_A>>(*d_a1) : nullptr};
    }
  }

  __attribute__((pure)) static List<t_A> nil() { return List(Nil{}); }

  __attribute__((pure)) static List<t_A> cons(t_A a0, List<t_A> a1) {
    return List(
        Cons{std::move(a0), std::make_unique<List<t_A>>(std::move(a1))});
  }

  // MANIPULATORS
  inline variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }

  __attribute__((pure)) List<t_A> app(List<t_A> m) const {
    auto &&_sv = *(this);
    if (std::holds_alternative<typename List<t_A>::Nil>(_sv.v())) {
      return m;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<t_A>::Cons>(_sv.v());
      return List<t_A>::cons(d_a0, (*(d_a1)).app(std::move(m)));
    }
  }
};

struct NameClashScopeLeak {
  /// Match on list, return list. Both branches produce the same type.
  __attribute__((pure)) static List<unsigned int>
  rotate(const List<unsigned int> &l);
  /// Two consecutive matches on different lists in the same function.
  __attribute__((pure)) static unsigned int
  heads_sum(const List<unsigned int> &l1, const List<unsigned int> &l2);
  /// Match on list, and in the Cons branch, match on the tail.
  __attribute__((pure)) static unsigned int
  first_two_sum(const List<unsigned int> &l);
  /// Match where both branches contain let bindings with same name.
  __attribute__((pure)) static unsigned int
  branch_let_clash(const List<unsigned int> &l);
  /// Three consecutive matches, each with same binding variable name pattern.
  __attribute__((pure)) static unsigned int
  triple_head(const List<unsigned int> &l1, const List<unsigned int> &l2,
              const List<unsigned int> &l3);
  /// Matching on a pair where both components are lists.
  __attribute__((pure)) static unsigned int
  pair_match(const std::pair<List<unsigned int>, List<unsigned int>> &p);
};

#endif // INCLUDED_NAME_CLASH_SCOPE_LEAK
