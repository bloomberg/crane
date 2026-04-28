#ifndef INCLUDED_FIX_ESCAPE_MATCH
#define INCLUDED_FIX_ESCAPE_MATCH

#include <functional>
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
};

struct FixEscapeMatch {
  /// A local fixpoint inside a match branch capturing a pattern variable.
  /// The pattern variable h is a structured binding reference into the
  /// shared_ptr's data. The fixpoint captures it by &, then escapes
  /// through an option constructor. After the match IIFE returns,
  /// h is destroyed — invoking the closure is use-after-free.
  __attribute__((
      pure)) static std::optional<std::function<unsigned int(unsigned int)>>
  make_fn_from_head(const List<unsigned int> &l);
  static inline const unsigned int test_match = []() -> unsigned int {
    auto _cs = make_fn_from_head(
        List<unsigned int>::cons(10u, List<unsigned int>::nil()));
    if (_cs.has_value()) {
      const std::function<unsigned int(unsigned int)> &f = *_cs;
      return f(3u);
    } else {
      return 0u;
    }
  }();
  /// Variant: fixpoint captures TWO pattern variables from the match.
  __attribute__((
      pure)) static std::optional<std::function<unsigned int(unsigned int)>>
  make_fn_from_pair(const List<unsigned int> &l);
  static inline const unsigned int test_match2 = []() -> unsigned int {
    auto _cs = make_fn_from_pair(List<unsigned int>::cons(
        10u, List<unsigned int>::cons(20u, List<unsigned int>::nil())));
    if (_cs.has_value()) {
      const std::function<unsigned int(unsigned int)> &f = *_cs;
      return f(3u);
    } else {
      return 0u;
    }
  }();
};

#endif // INCLUDED_FIX_ESCAPE_MATCH
