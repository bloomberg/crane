#ifndef INCLUDED_HIGHER_ORDER
#define INCLUDED_HIGHER_ORDER

#include <any>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

struct HigherOrder {
  /// A simple polymorphic list type.
  template <typename A> struct list {
    // TYPES
    struct Nil {};

    struct Cons {
      A a0;
      std::shared_ptr<list<A>> a1;
    };

    using variant_t = std::variant<Nil, Cons>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    list() {}

    explicit list(Nil _v) : v_(_v) {}

    explicit list(Cons _v) : v_(std::move(_v)) {}

    template <typename _U> explicit list(const list<_U> &_other) {
      if (std::holds_alternative<typename list<_U>::Nil>(_other.v())) {
        this->v_ = Nil{};
      } else {
        const auto &[a0, a1] = std::get<typename list<_U>::Cons>(_other.v());
        this->v_ = Cons{
            [&]() -> A {
              if constexpr (std::is_same_v<_U, std::any>) {
                if (a0.type() == typeid(A))
                  return std::any_cast<A>(a0);
                if constexpr (requires {
                                typename A::first_type;
                                typename A::second_type;
                              }) {
                  const auto &[_k, _v] =
                      std::any_cast<std::pair<std::any, std::any>>(a0);
                  return A{
                      [&]() -> typename A::first_type {
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
                return std::any_cast<A>(a0);
              } else
                return A(a0);
            }(),
            a1 ? std::make_shared<list<A>>(*a1) : nullptr};
      }
    }

    static list<A> nil() { return list(Nil{}); }

    static list<A> cons(A a0, list<A> a1) {
      return list(
          Cons{std::move(a0), std::make_shared<list<A>>(std::move(a1))});
    }

    // MANIPULATORS
    ~list() {
      std::vector<std::shared_ptr<list<A>>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<Cons>(&_v)) {
          if (_alt->a1) {
            _stack.push_back(std::move(_alt->a1));
          }
        }
      };
      _drain(v_mut());
      while (!_stack.empty()) {
        auto _cur = std::move(_stack.back());
        _stack.pop_back();
        if (_cur.use_count() == 1) {
          _drain(_cur->v_mut());
        }
      }
    }

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename T2, typename F1>
    requires std::is_invocable_r_v<T2, F1 &, T1 &, list<T1> &, T2 &>
  static T2 list_rect(T2 f, F1 &&f0, const list<T1> &l) {
    if (std::holds_alternative<typename list<T1>::Nil>(l.v())) {
      return f;
    } else {
      const auto &[a0, a1] = std::get<typename list<T1>::Cons>(l.v());
      return f0(a0, *a1, list_rect<T1, T2>(f, f0, *a1));
    }
  }

  template <typename T1, typename T2, typename F1>
    requires std::is_invocable_r_v<T2, F1 &, T1 &, list<T1> &, T2 &>
  static T2 list_rec(T2 f, F1 &&f0, const list<T1> &l) {
    if (std::holds_alternative<typename list<T1>::Nil>(l.v())) {
      return f;
    } else {
      const auto &[a0, a1] = std::get<typename list<T1>::Cons>(l.v());
      return f0(a0, *a1, list_rec<T1, T2>(f, f0, *a1));
    }
  }

  /// map f l applies f to each element of l, producing a new list.
  template <typename T1, typename T2, typename F0>
    requires std::is_invocable_r_v<T2, F0 &, T1 &>
  static list<T2> map(F0 &&f, const list<T1> &l) {
    if (std::holds_alternative<typename list<T1>::Nil>(l.v())) {
      return list<T2>::nil();
    } else {
      const auto &[a0, a1] = std::get<typename list<T1>::Cons>(l.v());
      return list<T2>::cons(f(a0), map<T1, T2>(f, *a1));
    }
  }

  /// foldr f z l folds l from the right using f with initial
  /// accumulator z.
  template <typename T1, typename T2, typename F0>
    requires std::is_invocable_r_v<T2, F0 &, T1 &, T2 &>
  static T2 foldr(F0 &&f, T2 z, const list<T1> &l) {
    if (std::holds_alternative<typename list<T1>::Nil>(l.v())) {
      return z;
    } else {
      const auto &[a0, a1] = std::get<typename list<T1>::Cons>(l.v());
      return f(a0, foldr<T1, T2>(f, z, *a1));
    }
  }

  /// foldl f z l folds l from the left using f with initial
  /// accumulator z. This is tail-recursive.
  template <typename T1, typename T2, typename F0>
    requires std::is_invocable_r_v<T2, F0 &, T2 &, T1 &>
  static T2 foldl(F0 &&f, T2 z, const list<T1> &l) {
    if (std::holds_alternative<typename list<T1>::Nil>(l.v())) {
      return z;
    } else {
      const auto &[a0, a1] = std::get<typename list<T1>::Cons>(l.v());
      return foldl<T1, T2>(f, f(z, a0), *a1);
    }
  }

  /// compose g f returns the composition of g after f.
  template <typename T1, typename T2, typename T3, typename F0, typename F1>
    requires std::is_invocable_r_v<T3, F0 &, T2 &> &&
             std::is_invocable_r_v<T2, F1 &, T1 &>
  static T3 compose(F0 &&g, F1 &&f, const T1 &x) {
    return g(f(x));
  }

  /// iterate n f x applies f to x a total of n times.
  template <typename T1, typename F1>
    requires std::is_invocable_r_v<T1, F1 &, T1 &>
  static T1 iterate(uint64_t n, F1 &&f, T1 x) {
    if (n <= 0) {
      return x;
    } else {
      uint64_t m = n - 1;
      return f(iterate<T1>(m, f, x));
    }
  }

  /// adder n returns a function that adds n to its argument.
  static uint64_t adder(uint64_t _x0, uint64_t _x1);

  /// twice f returns a function that applies f two times.
  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, T1 &>
  static T1 twice(F0 &&f, const T1 &x) {
    return f(f(x));
  }

  /// pipe x f applies f to x, simulating a pipeline operator.
  template <typename T1, typename T2, typename F1>
    requires std::is_invocable_r_v<T2, F1 &, T1 &>
  static T2 pipe(const T1 &x, F1 &&f) {
    return f(x);
  }

  static inline const list<uint64_t> test_list = list<uint64_t>::cons(
      UINT64_C(1),
      list<uint64_t>::cons(
          UINT64_C(2),
          list<uint64_t>::cons(
              UINT64_C(3),
              list<uint64_t>::cons(
                  UINT64_C(4),
                  list<uint64_t>::cons(UINT64_C(5), list<uint64_t>::nil())))));
  static inline const uint64_t test_map = foldr<uint64_t, uint64_t>(
      [](uint64_t _x0, uint64_t _x1) -> uint64_t { return (_x0 + _x1); },
      UINT64_C(0),
      map<uint64_t, uint64_t>(
          [](uint64_t _x0) -> uint64_t { return (UINT64_C(1) + _x0); },
          test_list));
  static inline const uint64_t test_foldr = foldr<uint64_t, uint64_t>(
      [](uint64_t _x0, uint64_t _x1) -> uint64_t { return (_x0 + _x1); },
      UINT64_C(0), test_list);
  static inline const uint64_t test_foldl = foldl<uint64_t, uint64_t>(
      [](uint64_t _x0, uint64_t _x1) -> uint64_t { return (_x0 + _x1); },
      UINT64_C(0), test_list);
  static inline const uint64_t test_compose =
      compose<uint64_t, uint64_t, uint64_t>(
          [](uint64_t _x0) -> uint64_t { return (UINT64_C(2) * _x0); },
          [](uint64_t _x0) -> uint64_t { return (UINT64_C(1) + _x0); },
          UINT64_C(3));
  static inline const uint64_t test_iterate = iterate<uint64_t>(
      UINT64_C(3), [](uint64_t _x0) -> uint64_t { return (UINT64_C(2) + _x0); },
      UINT64_C(0));
  static inline const uint64_t test_adder = adder(UINT64_C(5), UINT64_C(3));
  static inline const uint64_t test_twice = twice<uint64_t>(
      [](uint64_t _x0) -> uint64_t { return (UINT64_C(1) + _x0); },
      UINT64_C(5));
  static inline const uint64_t test_pipe =
      pipe<uint64_t, uint64_t>(UINT64_C(5), [](uint64_t _x0) -> uint64_t {
        return adder(UINT64_C(3), _x0);
      });
};

#endif // INCLUDED_HIGHER_ORDER
