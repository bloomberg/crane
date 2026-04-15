#ifndef INCLUDED_LOOPIFY_ADVANCED_PATTERNS
#define INCLUDED_LOOPIFY_ADVANCED_PATTERNS

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

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

struct LoopifyAdvancedPatterns {
  __attribute__((pure)) static unsigned int
  len_impl(const std::shared_ptr<List<unsigned int>> &l);
  static std::shared_ptr<List<unsigned int>>
  as_guard(const std::shared_ptr<List<unsigned int>> &l);
  __attribute__((pure)) static unsigned int
  multi_guard(const std::shared_ptr<List<unsigned int>> &l);
  __attribute__((pure)) static unsigned int
  four_elem(const std::shared_ptr<List<unsigned int>> &l);
  __attribute__((pure)) static unsigned int nested_pattern(
      const std::shared_ptr<
          List<std::pair<std::pair<unsigned int, unsigned int>, unsigned int>>>
          &l);
  __attribute__((pure)) static unsigned int
  guard_accum(const unsigned int acc,
              const std::shared_ptr<List<unsigned int>> &l);
  static std::shared_ptr<List<unsigned int>>
  cons_computed(const unsigned int n,
                const std::shared_ptr<List<unsigned int>> &l);

  struct shape {
    // TYPES
    struct Circle {
      unsigned int d_a0;
    };

    struct Square {
      unsigned int d_a0;
    };

    struct Triangle {
      unsigned int d_a0;
    };

    using variant_t = std::variant<Circle, Square, Triangle>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    explicit shape(Circle _v) : d_v_(std::move(_v)) {}

    explicit shape(Square _v) : d_v_(std::move(_v)) {}

    explicit shape(Triangle _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<shape> circle(unsigned int a0) {
      return std::make_shared<shape>(Circle{std::move(a0)});
    }

    static std::shared_ptr<shape> square(unsigned int a0) {
      return std::make_shared<shape>(Square{std::move(a0)});
    }

    static std::shared_ptr<shape> triangle(unsigned int a0) {
      return std::make_shared<shape>(Triangle{std::move(a0)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, unsigned int> F0,
            MapsTo<T1, unsigned int> F1, MapsTo<T1, unsigned int> F2>
  static T1 shape_rect(F0 &&f, F1 &&f0, F2 &&f1,
                       const std::shared_ptr<shape> &s) {
    if (std::holds_alternative<typename shape::Circle>(s->v())) {
      const auto &[d_a0] = std::get<typename shape::Circle>(s->v());
      return f(d_a0);
    } else if (std::holds_alternative<typename shape::Square>(s->v())) {
      const auto &[d_a0] = std::get<typename shape::Square>(s->v());
      return f0(d_a0);
    } else {
      const auto &[d_a0] = std::get<typename shape::Triangle>(s->v());
      return f1(d_a0);
    }
  }

  template <typename T1, MapsTo<T1, unsigned int> F0,
            MapsTo<T1, unsigned int> F1, MapsTo<T1, unsigned int> F2>
  static T1 shape_rec(F0 &&f, F1 &&f0, F2 &&f1,
                      const std::shared_ptr<shape> &s) {
    if (std::holds_alternative<typename shape::Circle>(s->v())) {
      const auto &[d_a0] = std::get<typename shape::Circle>(s->v());
      return f(d_a0);
    } else if (std::holds_alternative<typename shape::Square>(s->v())) {
      const auto &[d_a0] = std::get<typename shape::Square>(s->v());
      return f0(d_a0);
    } else {
      const auto &[d_a0] = std::get<typename shape::Triangle>(s->v());
      return f1(d_a0);
    }
  }

  __attribute__((pure)) static unsigned int
  extract_value(const std::shared_ptr<shape> &s);
  __attribute__((pure)) static unsigned int
  sum_shapes(const std::shared_ptr<List<std::shared_ptr<shape>>> &l);
  __attribute__((pure)) static std::pair<std::pair<unsigned int, unsigned int>,
                                         unsigned int>
  count_by_shape(const std::shared_ptr<List<std::shared_ptr<shape>>> &l);
  static std::shared_ptr<List<unsigned int>>
  replace_at(const unsigned int idx, const unsigned int value,
             const std::shared_ptr<List<unsigned int>> &l);
};

#endif // INCLUDED_LOOPIFY_ADVANCED_PATTERNS
