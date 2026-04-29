#ifndef INCLUDED_FUNCTION_VERNAC
#define INCLUDED_FUNCTION_VERNAC

#include <any>
#include <functional>
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
  ~List() {
    std::vector<std::unique_ptr<List>> _stack;
    auto _drain = [&](List &_node) {
      if (std::holds_alternative<Cons>(_node.d_v_)) {
        auto &_alt = std::get<Cons>(_node.d_v_);
        if (_alt.d_a1)
          _stack.push_back(std::move(_alt.d_a1));
      }
    };
    _drain(*this);
    while (!_stack.empty()) {
      auto _node = std::move(_stack.back());
      _stack.pop_back();
      if (_node)
        _drain(*_node);
    }
  }

  inline variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
};

template <typename t_A> struct Sig {
  // TYPES
  struct Exist {
    t_A d_x;
  };

  using variant_t = std::variant<Exist>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  Sig() {}

  explicit Sig(Exist _v) : d_v_(std::move(_v)) {}

  Sig(const Sig<t_A> &_other) : d_v_(std::move(_other.clone().d_v_)) {}

  Sig(Sig<t_A> &&_other) : d_v_(std::move(_other.d_v_)) {}

  Sig<t_A> &operator=(const Sig<t_A> &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  Sig<t_A> &operator=(Sig<t_A> &&_other) {
    d_v_ = std::move(_other.d_v_);
    return *this;
  }

  // ACCESSORS
  __attribute__((pure)) Sig<t_A> clone() const {
    auto &&_sv = *(this);
    const auto &[d_x] = std::get<Exist>(_sv.v());
    return Sig<t_A>(Exist{d_x});
  }

  // CREATORS
  template <typename _U> explicit Sig(const Sig<_U> &_other) {
    const auto &[d_x] = std::get<typename Sig<_U>::Exist>(_other.v());
    d_v_ = Exist{t_A(d_x)};
  }

  __attribute__((pure)) static Sig<t_A> exist(t_A x) {
    return Sig(Exist{std::move(x)});
  }

  // MANIPULATORS
  inline variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
};

struct FunctionVernac {
  template <MapsTo<unsigned int, unsigned int> F0>
  __attribute__((pure)) static unsigned int div2_F(F0 &&div3,
                                                   const unsigned int &n) {
    if (n <= 0) {
      return 0u;
    } else {
      unsigned int n0 = n - 1;
      if (n0 <= 0) {
        return 0u;
      } else {
        unsigned int p = n0 - 1;
        return (div3(p) + 1);
      }
    }
  }

  __attribute__((pure)) static Sig<unsigned int>
  div2_terminate(const unsigned int &n);
  __attribute__((pure)) static unsigned int div2(const unsigned int &n);

  struct R_div2 {
    // TYPES
    struct R_div2_0 {
      unsigned int d_n;
    };

    struct R_div2_1 {
      unsigned int d_n;
    };

    struct R_div2_2 {
      unsigned int d_n;
      unsigned int d_p;
      unsigned int d_a2;
      std::unique_ptr<R_div2> d__res;
    };

    using variant_t = std::variant<R_div2_0, R_div2_1, R_div2_2>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    R_div2() {}

    explicit R_div2(R_div2_0 _v) : d_v_(std::move(_v)) {}

    explicit R_div2(R_div2_1 _v) : d_v_(std::move(_v)) {}

    explicit R_div2(R_div2_2 _v) : d_v_(std::move(_v)) {}

    R_div2(const R_div2 &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    R_div2(R_div2 &&_other) : d_v_(std::move(_other.d_v_)) {}

    R_div2 &operator=(const R_div2 &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    R_div2 &operator=(R_div2 &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) R_div2 clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<R_div2_0>(_sv.v())) {
        const auto &[d_n] = std::get<R_div2_0>(_sv.v());
        return R_div2(R_div2_0{d_n});
      } else if (std::holds_alternative<R_div2_1>(_sv.v())) {
        const auto &[d_n] = std::get<R_div2_1>(_sv.v());
        return R_div2(R_div2_1{d_n});
      } else {
        const auto &[d_n, d_p, d_a2, d__res] = std::get<R_div2_2>(_sv.v());
        return R_div2(R_div2_2{
            d_n, d_p, d_a2,
            d__res ? std::make_unique<FunctionVernac::R_div2>(d__res->clone())
                   : nullptr});
      }
    }

    // CREATORS
    __attribute__((pure)) static R_div2 r_div2_0(unsigned int n) {
      return R_div2(R_div2_0{std::move(n)});
    }

    __attribute__((pure)) static R_div2 r_div2_1(unsigned int n) {
      return R_div2(R_div2_1{std::move(n)});
    }

    __attribute__((pure)) static R_div2 r_div2_2(unsigned int n, unsigned int p,
                                                 unsigned int a2, R_div2 _res) {
      return R_div2(R_div2_2{std::move(n), std::move(p), std::move(a2),
                             std::make_unique<R_div2>(std::move(_res))});
    }

    // MANIPULATORS
    ~R_div2() {
      std::vector<std::unique_ptr<R_div2>> _stack;
      auto _drain = [&](R_div2 &_node) {
        if (std::holds_alternative<R_div2_2>(_node.d_v_)) {
          auto &_alt = std::get<R_div2_2>(_node.d_v_);
          if (_alt.d__res)
            _stack.push_back(std::move(_alt.d__res));
        }
      };
      _drain(*this);
      while (!_stack.empty()) {
        auto _node = std::move(_stack.back());
        _stack.pop_back();
        if (_node)
          _drain(*_node);
      }
    }

    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    template <
        typename T1, MapsTo<T1, unsigned int> F0, MapsTo<T1, unsigned int> F1,
        MapsTo<T1, unsigned int, unsigned int, unsigned int, R_div2, T1> F2>
    T1 R_div2_rec(F0 &&f, F1 &&f0, F2 &&f1, const unsigned int &,
                  const unsigned int &) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename R_div2::R_div2_0>(_sv.v())) {
        const auto &[d_n] = std::get<typename R_div2::R_div2_0>(_sv.v());
        return f(d_n);
      } else if (std::holds_alternative<typename R_div2::R_div2_1>(_sv.v())) {
        const auto &[d_n] = std::get<typename R_div2::R_div2_1>(_sv.v());
        return f0(d_n);
      } else {
        const auto &[d_n, d_p, d_a2, d__res] =
            std::get<typename R_div2::R_div2_2>(_sv.v());
        return f1(d_n, d_p, d_a2, *(d__res),
                  (*(d__res)).template R_div2_rec<T1>(f, f0, f1, d_p, d_a2));
      }
    }

    template <
        typename T1, MapsTo<T1, unsigned int> F0, MapsTo<T1, unsigned int> F1,
        MapsTo<T1, unsigned int, unsigned int, unsigned int, R_div2, T1> F2>
    T1 R_div2_rect(F0 &&f, F1 &&f0, F2 &&f1, const unsigned int &,
                   const unsigned int &) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename R_div2::R_div2_0>(_sv.v())) {
        const auto &[d_n] = std::get<typename R_div2::R_div2_0>(_sv.v());
        return f(d_n);
      } else if (std::holds_alternative<typename R_div2::R_div2_1>(_sv.v())) {
        const auto &[d_n] = std::get<typename R_div2::R_div2_1>(_sv.v());
        return f0(d_n);
      } else {
        const auto &[d_n, d_p, d_a2, d__res] =
            std::get<typename R_div2::R_div2_2>(_sv.v());
        return f1(d_n, d_p, d_a2, *(d__res),
                  (*(d__res)).template R_div2_rect<T1>(f, f0, f1, d_p, d_a2));
      }
    }
  };

  template <typename T1, MapsTo<T1, unsigned int> F0,
            MapsTo<T1, unsigned int> F1,
            MapsTo<T1, unsigned int, unsigned int, T1> F2>
  static T1 div2_rect(F0 &&f, F1 &&f0, F2 &&f1, const unsigned int &n) {
    std::function<T1(unsigned int, T1)> f2 =
        [=](unsigned int _pa0, T1 _pa1) mutable { return f1(n, _pa0, _pa1); };
    T1 f3 = std::any_cast<T1>(f0(n));
    T1 f4 = std::any_cast<T1>(f(n));
    if (n <= 0) {
      return f4;
    } else {
      unsigned int n0 = n - 1;
      if (n0 <= 0) {
        return f3;
      } else {
        unsigned int n1 = n0 - 1;
        std::function<T1(T1)> f5 = [=](T1 _pa0) mutable {
          return f2(n1, _pa0);
        };
        T1 hrec = div2_rect<T1>(f, f0, f1, n1);
        return f5(hrec);
      }
    }
  }

  template <typename T1, MapsTo<T1, unsigned int> F0,
            MapsTo<T1, unsigned int> F1,
            MapsTo<T1, unsigned int, unsigned int, T1> F2>
  static T1 div2_rec(F0 &&_x0, F1 &&_x1, F2 &&_x2, const unsigned int &_x3) {
    return div2_rect<T1>(_x0, _x1, _x2, _x3);
  }

  __attribute__((pure)) static R_div2 R_div2_correct(const unsigned int &n,
                                                     const unsigned int &_res);

  template <MapsTo<unsigned int, List<unsigned int>> F0>
  __attribute__((pure)) static unsigned int
  list_sum_F(F0 &&list_sum0, const List<unsigned int> &l) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
      return 0u;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(l.v());
      return (d_a0 + list_sum0(*(d_a1)));
    }
  }

  __attribute__((pure)) static Sig<unsigned int>
  list_sum_terminate(const List<unsigned int> &l);
  __attribute__((pure)) static unsigned int
  list_sum(const List<unsigned int> &l);

  struct R_list_sum {
    // TYPES
    struct R_list_sum_0 {
      List<unsigned int> d_l;
    };

    struct R_list_sum_1 {
      List<unsigned int> d_l;
      unsigned int d_x;
      List<unsigned int> d_xs;
      unsigned int d_a3;
      std::unique_ptr<R_list_sum> d__res;
    };

    using variant_t = std::variant<R_list_sum_0, R_list_sum_1>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    R_list_sum() {}

    explicit R_list_sum(R_list_sum_0 _v) : d_v_(std::move(_v)) {}

    explicit R_list_sum(R_list_sum_1 _v) : d_v_(std::move(_v)) {}

    R_list_sum(const R_list_sum &_other)
        : d_v_(std::move(_other.clone().d_v_)) {}

    R_list_sum(R_list_sum &&_other) : d_v_(std::move(_other.d_v_)) {}

    R_list_sum &operator=(const R_list_sum &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    R_list_sum &operator=(R_list_sum &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) R_list_sum clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<R_list_sum_0>(_sv.v())) {
        const auto &[d_l] = std::get<R_list_sum_0>(_sv.v());
        return R_list_sum(R_list_sum_0{d_l.clone()});
      } else {
        const auto &[d_l, d_x, d_xs, d_a3, d__res] =
            std::get<R_list_sum_1>(_sv.v());
        return R_list_sum(R_list_sum_1{
            d_l.clone(), d_x, d_xs.clone(), d_a3,
            d__res
                ? std::make_unique<FunctionVernac::R_list_sum>(d__res->clone())
                : nullptr});
      }
    }

    // CREATORS
    __attribute__((pure)) static R_list_sum r_list_sum_0(List<unsigned int> l) {
      return R_list_sum(R_list_sum_0{std::move(l)});
    }

    __attribute__((pure)) static R_list_sum
    r_list_sum_1(List<unsigned int> l, unsigned int x, List<unsigned int> xs,
                 unsigned int a3, R_list_sum _res) {
      return R_list_sum(
          R_list_sum_1{std::move(l), std::move(x), std::move(xs), std::move(a3),
                       std::make_unique<R_list_sum>(std::move(_res))});
    }

    // MANIPULATORS
    ~R_list_sum() {
      std::vector<std::unique_ptr<R_list_sum>> _stack;
      auto _drain = [&](R_list_sum &_node) {
        if (std::holds_alternative<R_list_sum_1>(_node.d_v_)) {
          auto &_alt = std::get<R_list_sum_1>(_node.d_v_);
          if (_alt.d__res)
            _stack.push_back(std::move(_alt.d__res));
        }
      };
      _drain(*this);
      while (!_stack.empty()) {
        auto _node = std::move(_stack.back());
        _stack.pop_back();
        if (_node)
          _drain(*_node);
      }
    }

    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    template <typename T1, MapsTo<T1, List<unsigned int>> F0,
              MapsTo<T1, List<unsigned int>, unsigned int, List<unsigned int>,
                     unsigned int, R_list_sum, T1>
                  F1>
    T1 R_list_sum_rec(F0 &&f, F1 &&f0, const List<unsigned int> &,
                      const unsigned int &) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename R_list_sum::R_list_sum_0>(_sv.v())) {
        const auto &[d_l] =
            std::get<typename R_list_sum::R_list_sum_0>(_sv.v());
        return f(d_l);
      } else {
        const auto &[d_l, d_x, d_xs, d_a3, d__res] =
            std::get<typename R_list_sum::R_list_sum_1>(_sv.v());
        return f0(d_l, d_x, d_xs, d_a3, *(d__res),
                  (*(d__res)).template R_list_sum_rec<T1>(f, f0, d_xs, d_a3));
      }
    }

    template <typename T1, MapsTo<T1, List<unsigned int>> F0,
              MapsTo<T1, List<unsigned int>, unsigned int, List<unsigned int>,
                     unsigned int, R_list_sum, T1>
                  F1>
    T1 R_list_sum_rect(F0 &&f, F1 &&f0, const List<unsigned int> &,
                       const unsigned int &) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename R_list_sum::R_list_sum_0>(_sv.v())) {
        const auto &[d_l] =
            std::get<typename R_list_sum::R_list_sum_0>(_sv.v());
        return f(d_l);
      } else {
        const auto &[d_l, d_x, d_xs, d_a3, d__res] =
            std::get<typename R_list_sum::R_list_sum_1>(_sv.v());
        return f0(d_l, d_x, d_xs, d_a3, *(d__res),
                  (*(d__res)).template R_list_sum_rect<T1>(f, f0, d_xs, d_a3));
      }
    }
  };

  template <
      typename T1, MapsTo<T1, List<unsigned int>> F0,
      MapsTo<T1, List<unsigned int>, unsigned int, List<unsigned int>, T1> F1>
  static T1 list_sum_rect(F0 &&f, F1 &&f0, const List<unsigned int> &l) {
    std::function<T1(unsigned int, List<unsigned int>, T1)> f1 =
        [=](unsigned int _pa0, List<unsigned int> _pa1, T1 _pa2) mutable {
          return f0(l, _pa0, _pa1, _pa2);
        };
    T1 f2 = std::any_cast<T1>(f(l));
    if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
      return f2;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(l.v());
      List<unsigned int> d_a1_value = List<unsigned int>(*(d_a1));
      std::function<T1(T1)> f3 = [=](T1 _pa0) mutable {
        return f1(d_a0, d_a1_value, _pa0);
      };
      T1 hrec = list_sum_rect<T1>(f, f0, d_a1_value);
      return f3(hrec);
    }
  }

  template <
      typename T1, MapsTo<T1, List<unsigned int>> F0,
      MapsTo<T1, List<unsigned int>, unsigned int, List<unsigned int>, T1> F1>
  static T1 list_sum_rec(F0 &&_x0, F1 &&_x1, const List<unsigned int> &_x2) {
    return list_sum_rect<T1>(_x0, _x1, _x2);
  }

  __attribute__((pure)) static R_list_sum
  R_list_sum_correct(const List<unsigned int> &l, const unsigned int &_res);
  static inline const unsigned int test_div2 = div2(10u);
  static inline const unsigned int test_sum = list_sum(List<unsigned int>::cons(
      1u, List<unsigned int>::cons(
              2u, List<unsigned int>::cons(
                      3u, List<unsigned int>::cons(
                              4u, List<unsigned int>::cons(
                                      5u, List<unsigned int>::nil()))))));
};

#endif // INCLUDED_FUNCTION_VERNAC
