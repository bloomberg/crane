#ifndef INCLUDED_FIX_ESCAPE_MATCH
#define INCLUDED_FIX_ESCAPE_MATCH

#include <any>
#include <functional>
#include <memory>
#include <optional>
#include <utility>
#include <variant>

template <typename A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    A a;
    std::shared_ptr<List<A>> l;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  List() {}

  explicit List(Nil _v) : v_(_v) {}

  explicit List(Cons _v) : v_(std::move(_v)) {}

  template <typename _U> explicit List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      this->v_ = Nil{};
    } else {
      const auto &[a, l] = std::get<typename List<_U>::Cons>(_other.v());
      this->v_ = Cons{
          [&]() -> A {
            if constexpr (std::is_same_v<_U, std::any>) {
              if (a.type() == typeid(A))
                return std::any_cast<A>(a);
              if constexpr (requires {
                              typename A::first_type;
                              typename A::second_type;
                            }) {
                const auto &[_k, _v] =
                    std::any_cast<std::pair<std::any, std::any>>(a);
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
              return std::any_cast<A>(a);
            } else
              return A(a);
          }(),
          l ? std::make_shared<List<A>>(*l) : nullptr};
    }
  }

  static List<A> nil() { return List(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List(Cons{std::move(a), std::make_shared<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct FixEscapeMatch {
  /// A local fixpoint inside a match branch capturing a pattern variable.
  /// The pattern variable h is a structured binding reference into the
  /// shared_ptr's data. The fixpoint captures it by &, then escapes
  /// through an option constructor. After the match IIFE returns,
  /// h is destroyed — invoking the closure is use-after-free.
  static std::optional<std::function<uint64_t(uint64_t)>>
  make_fn_from_head(const List<uint64_t> &l);
  static inline const uint64_t test_match = []() -> uint64_t {
    auto _cs = make_fn_from_head(
        List<uint64_t>::cons(UINT64_C(10), List<uint64_t>::nil()));
    if (_cs.has_value()) {
      const std::function<uint64_t(uint64_t)> &f = *_cs;
      return f(UINT64_C(3));
    } else {
      return UINT64_C(0);
    }
  }();
  /// Variant: fixpoint captures TWO pattern variables from the match.
  static std::optional<std::function<uint64_t(uint64_t)>>
  make_fn_from_pair(const List<uint64_t> &l);
  static inline const uint64_t test_match2 = []() -> uint64_t {
    auto _cs = make_fn_from_pair(List<uint64_t>::cons(
        UINT64_C(10),
        List<uint64_t>::cons(UINT64_C(20), List<uint64_t>::nil())));
    if (_cs.has_value()) {
      const std::function<uint64_t(uint64_t)> &f = *_cs;
      return f(UINT64_C(3));
    } else {
      return UINT64_C(0);
    }
  }();
};

#endif // INCLUDED_FIX_ESCAPE_MATCH
