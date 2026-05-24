#ifndef INCLUDED_FUNCTION_VERNAC
#define INCLUDED_FUNCTION_VERNAC

#include <any>
#include <functional>
#include <memory>
#include <type_traits>
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

template <typename A> struct Sig {
  // DATA
  A x;

  // ACCESSORS
  Sig<A> clone() const { return {x}; }

  // CREATORS
  static Sig<A> exist(A x) { return {std::move(x)}; }
};

struct FunctionVernac {
  template <typename F0>
    requires std::is_invocable_r_v<uint64_t, F0 &, uint64_t &>
  static uint64_t div2_F(F0 &&div3, uint64_t n) {
    if (n <= 0) {
      return UINT64_C(0);
    } else {
      uint64_t n0 = n - 1;
      if (n0 <= 0) {
        return UINT64_C(0);
      } else {
        uint64_t p = n0 - 1;
        return (div3(p) + 1);
      }
    }
  }

  static Sig<uint64_t> div2_terminate(uint64_t n);
  static uint64_t div2(uint64_t n);

  struct R_div2 {
    // TYPES
    struct R_div2_0 {
      uint64_t n;
    };

    struct R_div2_1 {
      uint64_t n;
    };

    struct R_div2_2 {
      uint64_t n;
      uint64_t p;
      uint64_t a2;
      std::shared_ptr<R_div2> _res;
    };

    using variant_t = std::variant<R_div2_0, R_div2_1, R_div2_2>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    R_div2() {}

    explicit R_div2(R_div2_0 _v) : v_(std::move(_v)) {}

    explicit R_div2(R_div2_1 _v) : v_(std::move(_v)) {}

    explicit R_div2(R_div2_2 _v) : v_(std::move(_v)) {}

    static R_div2 r_div2_0(uint64_t n) { return R_div2(R_div2_0{n}); }

    static R_div2 r_div2_1(uint64_t n) { return R_div2(R_div2_1{n}); }

    static R_div2 r_div2_2(uint64_t n, uint64_t p, uint64_t a2, R_div2 _res) {
      return R_div2(
          R_div2_2{n, p, a2, std::make_shared<R_div2>(std::move(_res))});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    template <typename T1, typename F0, typename F1, typename F2>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F1 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F2 &, uint64_t &, uint64_t &,
                                     uint64_t &, R_div2 &, T1 &>
    T1 R_div2_rec(F0 &&f, F1 &&f0, F2 &&f1, uint64_t, uint64_t) const {
      if (std::holds_alternative<typename R_div2::R_div2_0>(this->v())) {
        const auto &[n0] = std::get<typename R_div2::R_div2_0>(this->v());
        return f(n0);
      } else if (std::holds_alternative<typename R_div2::R_div2_1>(this->v())) {
        const auto &[n0] = std::get<typename R_div2::R_div2_1>(this->v());
        return f0(n0);
      } else {
        const auto &[n0, p0, a2, _res0] =
            std::get<typename R_div2::R_div2_2>(this->v());
        return f1(n0, p0, a2, *_res0,
                  _res0->template R_div2_rec<T1>(f, f0, f1, p0, a2));
      }
    }

    template <typename T1, typename F0, typename F1, typename F2>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F1 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F2 &, uint64_t &, uint64_t &,
                                     uint64_t &, R_div2 &, T1 &>
    T1 R_div2_rect(F0 &&f, F1 &&f0, F2 &&f1, uint64_t, uint64_t) const {
      if (std::holds_alternative<typename R_div2::R_div2_0>(this->v())) {
        const auto &[n0] = std::get<typename R_div2::R_div2_0>(this->v());
        return f(n0);
      } else if (std::holds_alternative<typename R_div2::R_div2_1>(this->v())) {
        const auto &[n0] = std::get<typename R_div2::R_div2_1>(this->v());
        return f0(n0);
      } else {
        const auto &[n0, p0, a2, _res0] =
            std::get<typename R_div2::R_div2_2>(this->v());
        return f1(n0, p0, a2, *_res0,
                  _res0->template R_div2_rect<T1>(f, f0, f1, p0, a2));
      }
    }
  };

  template <typename T1, typename F0, typename F1, typename F2>
    requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
             std::is_invocable_r_v<T1, F1 &, uint64_t &> &&
             std::is_invocable_r_v<T1, F2 &, uint64_t &, uint64_t &, T1 &>
  static T1 div2_rect(F0 &&f, F1 &&f0, F2 &&f1, uint64_t n) {
    std::function<T1(uint64_t, T1)> f2 = [=](uint64_t _pa0, T1 _pa1) mutable {
      return f1(n, _pa0, _pa1);
    };
    T1 f3 = f0(n);
    T1 f4 = f(n);
    if (n <= 0) {
      return f4;
    } else {
      uint64_t n0 = n - 1;
      if (n0 <= 0) {
        return f3;
      } else {
        uint64_t n1 = n0 - 1;
        std::function<T1(T1)> f5 = [=](T1 _pa0) mutable {
          return f2(n1, _pa0);
        };
        T1 hrec = div2_rect<T1>(f, f0, f1, n1);
        return f5(hrec);
      }
    }
  }

  template <typename T1, typename F0, typename F1, typename F2>
    requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
             std::is_invocable_r_v<T1, F1 &, uint64_t &> &&
             std::is_invocable_r_v<T1, F2 &, uint64_t &, uint64_t &, T1 &>
  static T1 div2_rec(F0 &&_x0, F1 &&_x1, F2 &&_x2, uint64_t _x3) {
    return div2_rect<T1>(_x0, _x1, _x2, _x3);
  }

  static R_div2 R_div2_correct(uint64_t n, uint64_t _res);

  template <typename F0>
    requires std::is_invocable_r_v<uint64_t, F0 &, List<uint64_t> &>
  static uint64_t list_sum_F(F0 &&list_sum0, const List<uint64_t> &l) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
      return UINT64_C(0);
    } else {
      const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
      return (a0 + list_sum0(*a1));
    }
  }

  static Sig<uint64_t> list_sum_terminate(const List<uint64_t> &l);
  static uint64_t list_sum(const List<uint64_t> &l);

  struct R_list_sum {
    // TYPES
    struct R_list_sum_0 {
      List<uint64_t> l;
    };

    struct R_list_sum_1 {
      List<uint64_t> l;
      uint64_t x;
      List<uint64_t> xs;
      uint64_t a3;
      std::shared_ptr<R_list_sum> _res;
    };

    using variant_t = std::variant<R_list_sum_0, R_list_sum_1>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    R_list_sum() {}

    explicit R_list_sum(R_list_sum_0 _v) : v_(std::move(_v)) {}

    explicit R_list_sum(R_list_sum_1 _v) : v_(std::move(_v)) {}

    static R_list_sum r_list_sum_0(List<uint64_t> l) {
      return R_list_sum(R_list_sum_0{std::move(l)});
    }

    static R_list_sum r_list_sum_1(List<uint64_t> l, uint64_t x,
                                   List<uint64_t> xs, uint64_t a3,
                                   R_list_sum _res) {
      return R_list_sum(
          R_list_sum_1{std::move(l), x, std::move(xs), a3,
                       std::make_shared<R_list_sum>(std::move(_res))});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    template <typename T1, typename F0, typename F1>
      requires std::is_invocable_r_v<T1, F0 &, List<uint64_t> &> &&
               std::is_invocable_r_v<T1, F1 &, List<uint64_t> &, uint64_t &,
                                     List<uint64_t> &, uint64_t &, R_list_sum &,
                                     T1 &>
    T1 R_list_sum_rec(F0 &&f, F1 &&f0, const List<uint64_t> &, uint64_t) const {
      if (std::holds_alternative<typename R_list_sum::R_list_sum_0>(
              this->v())) {
        const auto &[l0] =
            std::get<typename R_list_sum::R_list_sum_0>(this->v());
        return f(l0);
      } else {
        const auto &[l0, x0, xs0, a3, _res0] =
            std::get<typename R_list_sum::R_list_sum_1>(this->v());
        return f0(l0, x0, xs0, a3, *_res0,
                  _res0->template R_list_sum_rec<T1>(f, f0, xs0, a3));
      }
    }

    template <typename T1, typename F0, typename F1>
      requires std::is_invocable_r_v<T1, F0 &, List<uint64_t> &> &&
               std::is_invocable_r_v<T1, F1 &, List<uint64_t> &, uint64_t &,
                                     List<uint64_t> &, uint64_t &, R_list_sum &,
                                     T1 &>
    T1 R_list_sum_rect(F0 &&f, F1 &&f0, const List<uint64_t> &,
                       uint64_t) const {
      if (std::holds_alternative<typename R_list_sum::R_list_sum_0>(
              this->v())) {
        const auto &[l0] =
            std::get<typename R_list_sum::R_list_sum_0>(this->v());
        return f(l0);
      } else {
        const auto &[l0, x0, xs0, a3, _res0] =
            std::get<typename R_list_sum::R_list_sum_1>(this->v());
        return f0(l0, x0, xs0, a3, *_res0,
                  _res0->template R_list_sum_rect<T1>(f, f0, xs0, a3));
      }
    }
  };

  template <typename T1, typename F0, typename F1>
    requires std::is_invocable_r_v<T1, F0 &, List<uint64_t> &> &&
             std::is_invocable_r_v<T1, F1 &, List<uint64_t> &, uint64_t &,
                                   List<uint64_t> &, T1 &>
  static T1 list_sum_rect(F0 &&f, F1 &&f0, const List<uint64_t> &l) {
    std::function<T1(uint64_t, List<uint64_t>, T1)> f1 =
        [=](uint64_t _pa0, List<uint64_t> _pa1, T1 _pa2) mutable {
          return f0(l, _pa0, _pa1, _pa2);
        };
    T1 f2 = f(l);
    if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
      return f2;
    } else {
      const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
      const List<uint64_t> &a1_value = *a1;
      std::function<T1(T1)> f3 = [=](T1 _pa0) mutable {
        return f1(a0, a1_value, _pa0);
      };
      T1 hrec = list_sum_rect<T1>(f, f0, a1_value);
      return f3(hrec);
    }
  }

  template <typename T1, typename F0, typename F1>
    requires std::is_invocable_r_v<T1, F0 &, List<uint64_t> &> &&
             std::is_invocable_r_v<T1, F1 &, List<uint64_t> &, uint64_t &,
                                   List<uint64_t> &, T1 &>
  static T1 list_sum_rec(F0 &&_x0, F1 &&_x1, const List<uint64_t> &_x2) {
    return list_sum_rect<T1>(_x0, _x1, _x2);
  }

  static R_list_sum R_list_sum_correct(const List<uint64_t> &l, uint64_t _res);
  static inline const uint64_t test_div2 = div2(UINT64_C(10));
  static inline const uint64_t test_sum = list_sum(List<uint64_t>::cons(
      UINT64_C(1),
      List<uint64_t>::cons(
          UINT64_C(2),
          List<uint64_t>::cons(
              UINT64_C(3),
              List<uint64_t>::cons(
                  UINT64_C(4),
                  List<uint64_t>::cons(UINT64_C(5), List<uint64_t>::nil()))))));
};

#endif // INCLUDED_FUNCTION_VERNAC
