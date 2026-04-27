#ifndef INCLUDED_LOOPIFY_ADVANCED_PATTERNS
#define INCLUDED_LOOPIFY_ADVANCED_PATTERNS

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

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
  using crane_element_type = t_A;

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

  __attribute__((pure)) List<t_A> &operator=(const List<t_A> &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  __attribute__((pure)) List<t_A> &operator=(List<t_A> &&_other) {
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
      t_A __c0;
      if constexpr (
          requires { d_a0 ? 0 : 0; } && requires { *d_a0; } &&
          requires { d_a0->clone(); } && requires { d_a0.get(); }) {
        using _E = std::remove_cvref_t<decltype(*d_a0)>;
        __c0 = d_a0 ? std::make_unique<_E>(d_a0->clone()) : nullptr;
      } else if constexpr (requires { d_a0.clone(); }) {
        __c0 = d_a0.clone();
      } else {
        __c0 = d_a0;
      }
      return List<t_A>(
          Cons{std::move(__c0),
               d_a1 ? std::make_unique<List<t_A>>(d_a1->clone()) : nullptr});
    }
  }

  // CREATORS
  template <typename _U> explicit List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      d_v_ = Nil{};
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<_U>::Cons>(_other.v());
      d_v_ = Cons{
          [&]<typename _DstT = t_A>(auto &&__v) -> _DstT {
            if constexpr (
                requires { *__v; } &&
                !requires { std::declval<_DstT>().get(); })
              return _DstT(*__v);
            else if constexpr (
                !requires { *__v; } &&
                requires { std::declval<_DstT>().get(); }) {
              using _E =
                  std::remove_pointer_t<decltype(std::declval<_DstT>().get())>;
              return std::make_unique<_E>(std::move(__v));
            } else
              return _DstT(__v);
          }(d_a0),
          d_a1 ? std::make_unique<List<t_A>>(*d_a1) : nullptr};
    }
  }

  __attribute__((pure)) static List<t_A> nil() { return List(Nil{}); }

  __attribute__((pure)) static List<t_A> cons(t_A a0, const List<t_A> &a1) {
    return List(Cons{std::move(a0), std::make_unique<List<t_A>>(a1)});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) List<t_A> *operator->() { return this; }

  __attribute__((pure)) const List<t_A> *operator->() const { return this; }

  __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

  __attribute__((pure)) bool operator==(std::nullptr_t) const { return false; }

  // MANIPULATORS
  void reset() { *this = List<t_A>(); }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
};

struct LoopifyAdvancedPatterns {
  __attribute__((pure)) static unsigned int
  len_impl(const List<unsigned int> &l);
  __attribute__((pure)) static List<unsigned int>
  as_guard(const List<unsigned int> &l);
  __attribute__((pure)) static unsigned int
  multi_guard(const List<unsigned int> &l);
  __attribute__((pure)) static unsigned int
  four_elem(const List<unsigned int> &l);
  __attribute__((pure)) static unsigned int nested_pattern(
      const List<std::pair<std::pair<unsigned int, unsigned int>, unsigned int>>
          &l);
  __attribute__((pure)) static unsigned int
  guard_accum(unsigned int acc, const List<unsigned int> &l);
  __attribute__((pure)) static List<unsigned int>
  cons_computed(const unsigned int &n, const List<unsigned int> &l);

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
    shape() {}

    explicit shape(Circle _v) : d_v_(std::move(_v)) {}

    explicit shape(Square _v) : d_v_(std::move(_v)) {}

    explicit shape(Triangle _v) : d_v_(std::move(_v)) {}

    shape(const shape &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    shape(shape &&_other) : d_v_(std::move(_other.d_v_)) {}

    __attribute__((pure)) shape &operator=(const shape &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    __attribute__((pure)) shape &operator=(shape &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) shape clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<Circle>(_sv.v())) {
        const auto &[d_a0] = std::get<Circle>(_sv.v());
        return shape(Circle{[](auto &&__v) -> unsigned int {
          if constexpr (
              requires { __v ? 0 : 0; } && requires { *__v; } &&
              requires { __v->clone(); } && requires { __v.get(); }) {
            using _E = std::remove_cvref_t<decltype(*__v)>;
            return __v ? std::make_unique<_E>(__v->clone()) : nullptr;
          } else if constexpr (requires { __v.clone(); }) {
            return __v.clone();
          } else {
            return __v;
          }
        }(d_a0)});
      } else if (std::holds_alternative<Square>(_sv.v())) {
        const auto &[d_a0] = std::get<Square>(_sv.v());
        return shape(Square{[](auto &&__v) -> unsigned int {
          if constexpr (
              requires { __v ? 0 : 0; } && requires { *__v; } &&
              requires { __v->clone(); } && requires { __v.get(); }) {
            using _E = std::remove_cvref_t<decltype(*__v)>;
            return __v ? std::make_unique<_E>(__v->clone()) : nullptr;
          } else if constexpr (requires { __v.clone(); }) {
            return __v.clone();
          } else {
            return __v;
          }
        }(d_a0)});
      } else {
        const auto &[d_a0] = std::get<Triangle>(_sv.v());
        return shape(Triangle{[](auto &&__v) -> unsigned int {
          if constexpr (
              requires { __v ? 0 : 0; } && requires { *__v; } &&
              requires { __v->clone(); } && requires { __v.get(); }) {
            using _E = std::remove_cvref_t<decltype(*__v)>;
            return __v ? std::make_unique<_E>(__v->clone()) : nullptr;
          } else if constexpr (requires { __v.clone(); }) {
            return __v.clone();
          } else {
            return __v;
          }
        }(d_a0)});
      }
    }

    // CREATORS
    __attribute__((pure)) static shape circle(unsigned int a0) {
      return shape(Circle{std::move(a0)});
    }

    __attribute__((pure)) static shape square(unsigned int a0) {
      return shape(Square{std::move(a0)});
    }

    __attribute__((pure)) static shape triangle(unsigned int a0) {
      return shape(Triangle{std::move(a0)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) shape *operator->() { return this; }

    __attribute__((pure)) const shape *operator->() const { return this; }

    __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

    __attribute__((pure)) bool operator==(std::nullptr_t) const {
      return false;
    }

    // MANIPULATORS
    void reset() { *this = shape(); }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, unsigned int> F0,
            MapsTo<T1, unsigned int> F1, MapsTo<T1, unsigned int> F2>
  static T1 shape_rect(F0 &&f, F1 &&f0, F2 &&f1, const shape &s) {
    if (std::holds_alternative<typename shape::Circle>(s.v())) {
      const auto &[d_a0] = std::get<typename shape::Circle>(s.v());
      return f(d_a0);
    } else if (std::holds_alternative<typename shape::Square>(s.v())) {
      const auto &[d_a0] = std::get<typename shape::Square>(s.v());
      return f0(d_a0);
    } else {
      const auto &[d_a0] = std::get<typename shape::Triangle>(s.v());
      return f1(d_a0);
    }
  }

  template <typename T1, MapsTo<T1, unsigned int> F0,
            MapsTo<T1, unsigned int> F1, MapsTo<T1, unsigned int> F2>
  static T1 shape_rec(F0 &&f, F1 &&f0, F2 &&f1, const shape &s) {
    if (std::holds_alternative<typename shape::Circle>(s.v())) {
      const auto &[d_a0] = std::get<typename shape::Circle>(s.v());
      return f(d_a0);
    } else if (std::holds_alternative<typename shape::Square>(s.v())) {
      const auto &[d_a0] = std::get<typename shape::Square>(s.v());
      return f0(d_a0);
    } else {
      const auto &[d_a0] = std::get<typename shape::Triangle>(s.v());
      return f1(d_a0);
    }
  }

  __attribute__((pure)) static unsigned int extract_value(const shape &s);
  __attribute__((pure)) static unsigned int sum_shapes(const List<shape> &l);
  __attribute__((pure)) static std::pair<std::pair<unsigned int, unsigned int>,
                                         unsigned int>
  count_by_shape(const List<shape> &l);
  __attribute__((pure)) static List<unsigned int>
  replace_at(const unsigned int &idx, unsigned int value,
             const List<unsigned int> &l);
};

#endif // INCLUDED_LOOPIFY_ADVANCED_PATTERNS
