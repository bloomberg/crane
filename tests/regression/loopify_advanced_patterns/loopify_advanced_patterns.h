#ifndef INCLUDED_LOOPIFY_ADVANCED_PATTERNS
#define INCLUDED_LOOPIFY_ADVANCED_PATTERNS

#include <any>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

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

struct LoopifyAdvancedPatterns {
  static uint64_t len_impl(const List<uint64_t> &l);
  static List<uint64_t> as_guard(const List<uint64_t> &l);
  static uint64_t multi_guard(const List<uint64_t> &l);
  static uint64_t four_elem(const List<uint64_t> &l);
  static uint64_t nested_pattern(
      const List<std::pair<std::pair<uint64_t, uint64_t>, uint64_t>> &l);
  static uint64_t guard_accum(uint64_t acc, const List<uint64_t> &l);
  static List<uint64_t> cons_computed(uint64_t n, const List<uint64_t> &l);

  struct shape {
    // TYPES
    struct Circle {
      uint64_t a0;
    };

    struct Square {
      uint64_t a0;
    };

    struct Triangle {
      uint64_t a0;
    };

    using variant_t = std::variant<Circle, Square, Triangle>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    shape() {}

    explicit shape(Circle _v) : v_(std::move(_v)) {}

    explicit shape(Square _v) : v_(std::move(_v)) {}

    explicit shape(Triangle _v) : v_(std::move(_v)) {}

    static shape circle(uint64_t a0) { return shape(Circle{a0}); }

    static shape square(uint64_t a0) { return shape(Square{a0}); }

    static shape triangle(uint64_t a0) { return shape(Triangle{a0}); }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F0, typename F1, typename F2>
    requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
             std::is_invocable_r_v<T1, F1 &, uint64_t &> &&
             std::is_invocable_r_v<T1, F2 &, uint64_t &>
  static T1 shape_rect(F0 &&f, F1 &&f0, F2 &&f1, const shape &s) {
    if (std::holds_alternative<typename shape::Circle>(s.v())) {
      const auto &[a0] = std::get<typename shape::Circle>(s.v());
      return f(a0);
    } else if (std::holds_alternative<typename shape::Square>(s.v())) {
      const auto &[a0] = std::get<typename shape::Square>(s.v());
      return f0(a0);
    } else {
      const auto &[a0] = std::get<typename shape::Triangle>(s.v());
      return f1(a0);
    }
  }

  template <typename T1, typename F0, typename F1, typename F2>
    requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
             std::is_invocable_r_v<T1, F1 &, uint64_t &> &&
             std::is_invocable_r_v<T1, F2 &, uint64_t &>
  static T1 shape_rec(F0 &&f, F1 &&f0, F2 &&f1, const shape &s) {
    if (std::holds_alternative<typename shape::Circle>(s.v())) {
      const auto &[a0] = std::get<typename shape::Circle>(s.v());
      return f(a0);
    } else if (std::holds_alternative<typename shape::Square>(s.v())) {
      const auto &[a0] = std::get<typename shape::Square>(s.v());
      return f0(a0);
    } else {
      const auto &[a0] = std::get<typename shape::Triangle>(s.v());
      return f1(a0);
    }
  }

  static uint64_t extract_value(const shape &s);
  static uint64_t sum_shapes(const List<shape> &l);
  static std::pair<std::pair<uint64_t, uint64_t>, uint64_t>
  count_by_shape(const List<shape> &l);
  static List<uint64_t> replace_at(uint64_t idx, uint64_t value,
                                   const List<uint64_t> &l);
};

#endif // INCLUDED_LOOPIFY_ADVANCED_PATTERNS
