#ifndef INCLUDED_HIGHER_ORDER
#define INCLUDED_HIGHER_ORDER

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

struct HigherOrder {
  /// A simple polymorphic list type.
  template <typename t_A> struct list {
    // TYPES
    struct Nil {};

    struct Cons {
      t_A d_a0;
      std::unique_ptr<list<t_A>> d_a1;
    };

    using variant_t = std::variant<Nil, Cons>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    list() {}

    explicit list(Nil _v) : d_v_(_v) {}

    explicit list(Cons _v) : d_v_(std::move(_v)) {}

    list(const list<t_A> &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    list(list<t_A> &&_other) : d_v_(std::move(_other.d_v_)) {}

    list<t_A> &operator=(const list<t_A> &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    list<t_A> &operator=(list<t_A> &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) list<t_A> clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<Nil>(_sv.v())) {
        return list<t_A>(Nil{});
      } else {
        const auto &[d_a0, d_a1] = std::get<Cons>(_sv.v());
        return list<t_A>(Cons{
            d_a0, d_a1 ? std::make_unique<HigherOrder::list<t_A>>(d_a1->clone())
                       : nullptr});
      }
    }

    // CREATORS
    template <typename _U> explicit list(const list<_U> &_other) {
      if (std::holds_alternative<typename list<_U>::Nil>(_other.v())) {
        d_v_ = Nil{};
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename list<_U>::Cons>(_other.v());
        d_v_ = Cons{t_A(d_a0),
                    d_a1 ? std::make_unique<list<t_A>>(*d_a1) : nullptr};
      }
    }

    __attribute__((pure)) static list<t_A> nil() { return list(Nil{}); }

    __attribute__((pure)) static list<t_A> cons(t_A a0, const list<t_A> &a1) {
      return list(Cons{std::move(a0), std::make_unique<list<t_A>>(a1)});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) list<t_A> *operator->() { return this; }

    __attribute__((pure)) const list<t_A> *operator->() const { return this; }

    __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

    __attribute__((pure)) bool operator==(std::nullptr_t) const {
      return false;
    }

    // MANIPULATORS
    void reset() { *this = list<t_A>(); }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, typename T2, MapsTo<T2, T1, list<T1>, T2> F1>
  static T2 list_rect(const T2 f, F1 &&f0, const list<T1> &l) {
    if (std::holds_alternative<typename list<T1>::Nil>(l.v())) {
      return f;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename list<T1>::Cons>(l.v());
      return f0(d_a0, *(d_a1), list_rect<T1, T2>(f, f0, *(d_a1)));
    }
  }

  template <typename T1, typename T2, MapsTo<T2, T1, list<T1>, T2> F1>
  static T2 list_rec(const T2 f, F1 &&f0, const list<T1> &l) {
    if (std::holds_alternative<typename list<T1>::Nil>(l.v())) {
      return f;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename list<T1>::Cons>(l.v());
      return f0(d_a0, *(d_a1), list_rec<T1, T2>(f, f0, *(d_a1)));
    }
  }

  /// map f l applies f to each element of l, producing a new list.
  template <typename T1, typename T2, MapsTo<T2, T1> F0>
  __attribute__((pure)) static list<T2> map(F0 &&f, const list<T1> &l) {
    if (std::holds_alternative<typename list<T1>::Nil>(l.v())) {
      return list<T2>::nil();
    } else {
      const auto &[d_a0, d_a1] = std::get<typename list<T1>::Cons>(l.v());
      return list<T2>::cons(f(d_a0), map<T1, T2>(f, *(d_a1)));
    }
  }

  /// foldr f z l folds l from the right using f with initial
  /// accumulator z.
  template <typename T1, typename T2, MapsTo<T2, T1, T2> F0>
  static T2 foldr(F0 &&f, const T2 z, const list<T1> &l) {
    if (std::holds_alternative<typename list<T1>::Nil>(l.v())) {
      return z;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename list<T1>::Cons>(l.v());
      return f(d_a0, foldr<T1, T2>(f, z, *(d_a1)));
    }
  }

  /// foldl f z l folds l from the left using f with initial
  /// accumulator z. This is tail-recursive.
  template <typename T1, typename T2, MapsTo<T2, T2, T1> F0>
  static T2 foldl(F0 &&f, const T2 z, const list<T1> &l) {
    if (std::holds_alternative<typename list<T1>::Nil>(l.v())) {
      return z;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename list<T1>::Cons>(l.v());
      return foldl<T1, T2>(f, f(z, d_a0), *(d_a1));
    }
  } /// compose g f returns the composition of g after f.

  template <typename T1, typename T2 = void, typename T3, typename F0,
            typename F1>
  static T3 compose(F0 &&g, F1 &&f, const T1 x) {
    return g(f(x));
  }

  /// iterate n f x applies f to x a total of n times.
  template <typename T1, MapsTo<T1, T1> F1>
  static T1 iterate(const unsigned int &n, F1 &&f, const T1 x) {
    if (n <= 0) {
      return x;
    } else {
      unsigned int m = n - 1;
      return f(iterate<T1>(m, f, x));
    }
  }

  /// adder n returns a function that adds n to its argument.
  __attribute__((pure)) static unsigned int adder(const unsigned int &_x0,
                                                  const unsigned int &_x1);

  /// twice f returns a function that applies f two times.
  template <typename T1, MapsTo<T1, T1> F0>
  static T1 twice(F0 &&f, const T1 x) {
    return f(f(x));
  }

  /// pipe x f applies f to x, simulating a pipeline operator.
  template <typename T1, typename T2, MapsTo<T2, T1> F1>
  static T2 pipe(const T1 x, F1 &&f) {
    return f(x);
  }

  static inline const list<unsigned int> test_list = list<unsigned int>::cons(
      1u, list<unsigned int>::cons(
              2u, list<unsigned int>::cons(
                      3u, list<unsigned int>::cons(
                              4u, list<unsigned int>::cons(
                                      5u, list<unsigned int>::nil())))));
  static inline const unsigned int test_map = foldr<unsigned int, unsigned int>(
      [](unsigned int _x0, unsigned int _x1) -> unsigned int {
        return (_x0 + _x1);
      },
      0u,
      map<unsigned int, unsigned int>(
          [](unsigned int _x0) -> unsigned int { return (1u + _x0); },
          test_list));
  static inline const unsigned int test_foldr =
      foldr<unsigned int, unsigned int>(
          [](unsigned int _x0, unsigned int _x1) -> unsigned int {
            return (_x0 + _x1);
          },
          0u, test_list);
  static inline const unsigned int test_foldl =
      foldl<unsigned int, unsigned int>(
          [](unsigned int _x0, unsigned int _x1) -> unsigned int {
            return (_x0 + _x1);
          },
          0u, test_list);
  static inline const unsigned int test_compose =
      compose<unsigned int, unsigned int, unsigned int>(
          [](unsigned int _x0) -> unsigned int { return (2u * _x0); },
          [](unsigned int _x0) -> unsigned int { return (1u + _x0); }, 3u);
  static inline const unsigned int test_iterate = iterate<unsigned int>(
      3u, [](unsigned int _x0) -> unsigned int { return (2u + _x0); }, 0u);
  static inline const unsigned int test_adder = adder(5u, 3u);
  static inline const unsigned int test_twice = twice<unsigned int>(
      [](unsigned int _x0) -> unsigned int { return (1u + _x0); }, 5u);
  static inline const unsigned int test_pipe = pipe<unsigned int, unsigned int>(
      5u, [](unsigned int _x0) -> unsigned int { return adder(3u, _x0); });
};

#endif // INCLUDED_HIGHER_ORDER
