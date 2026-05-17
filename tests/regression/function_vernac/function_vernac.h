#ifndef INCLUDED_FUNCTION_VERNAC
#define INCLUDED_FUNCTION_VERNAC

#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

template <typename A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    A a0;
    std::unique_ptr<List<A>> a1;
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

  List(const List<A> &_other) : v_(std::move(_other.clone().v_)) {}

  List(List<A> &&_other) noexcept : v_(std::move(_other.v_)) {}

  List<A> &operator=(const List<A> &_other) {
    v_ = std::move(_other.clone().v_);
    return *this;
  }

  List<A> &operator=(List<A> &&_other) noexcept {
    v_ = std::move(_other.v_);
    return *this;
  }

  // ACCESSORS
  List<A> clone() const {
    List<A> _out{};

    struct _CloneFrame {
      const List<A> *_src;
      List<A> *_dst;
    };

    std::vector<_CloneFrame> _stack{};
    _stack.reserve(8);
    _stack.push_back({this, &_out});
    while (!_stack.empty()) {
      auto _frame = _stack.back();
      _stack.pop_back();
      const List<A> *_src = _frame._src;
      List<A> *_dst = _frame._dst;
      if (std::holds_alternative<Nil>(_src->v())) {
        _dst->v_ = Nil{};
      } else {
        const auto &_alt = std::get<Cons>(_src->v());
        _dst->v_ =
            Cons{_alt.a0, _alt.a1 ? std::make_unique<List<A>>() : nullptr};
        auto &_dst_alt = std::get<Cons>(_dst->v_);
        if (_alt.a1) {
          _stack.push_back({_alt.a1.get(), _dst_alt.a1.get()});
        }
      }
    }
    return _out;
  }

  // CREATORS
  template <typename _U> explicit List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      this->v_ = Nil{};
    } else {
      const auto &[a0, a1] = std::get<typename List<_U>::Cons>(_other.v());
      this->v_ = Cons{A(a0), a1 ? std::make_unique<List<A>>(*a1) : nullptr};
    }
  }

  static List<A> nil() { return List(Nil{}); }

  static List<A> cons(A a0, List<A> a1) {
    return List(Cons{std::move(a0), std::make_unique<List<A>>(std::move(a1))});
  }

  // MANIPULATORS
  ~List() {
    std::vector<std::unique_ptr<List<A>>> _stack{};
    _stack.reserve(8);
    auto _drain = [&](List<A> &_node) {
      if (std::holds_alternative<Cons>(_node.v_)) {
        auto &_alt = std::get<Cons>(_node.v_);
        if (_alt.a1) {
          _stack.push_back(std::move(_alt.a1));
        }
      }
    };
    _drain(*this);
    while (!_stack.empty()) {
      auto _node = std::move(_stack.back());
      _stack.pop_back();
      if (_node) {
        _drain(*_node);
      }
    }
  }

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
    requires std::is_invocable_r_v<unsigned int, F0 &, unsigned int &>
  static unsigned int div2_F(F0 &&div3, unsigned int n) {
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

  static Sig<unsigned int> div2_terminate(unsigned int n);
  static unsigned int div2(unsigned int n);

  struct R_div2 {
    // TYPES
    struct R_div2_0 {
      unsigned int n;
    };

    struct R_div2_1 {
      unsigned int n;
    };

    struct R_div2_2 {
      unsigned int n;
      unsigned int p;
      unsigned int a2;
      std::unique_ptr<R_div2> _res;
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

    R_div2(const R_div2 &_other) : v_(std::move(_other.clone().v_)) {}

    R_div2(R_div2 &&_other) noexcept : v_(std::move(_other.v_)) {}

    R_div2 &operator=(const R_div2 &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    R_div2 &operator=(R_div2 &&_other) noexcept {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    R_div2 clone() const {
      R_div2 _out{};

      struct _CloneFrame {
        const R_div2 *_src;
        R_div2 *_dst;
      };

      std::vector<_CloneFrame> _stack{};
      _stack.reserve(8);
      _stack.push_back({this, &_out});
      while (!_stack.empty()) {
        auto _frame = _stack.back();
        _stack.pop_back();
        const R_div2 *_src = _frame._src;
        R_div2 *_dst = _frame._dst;
        if (std::holds_alternative<R_div2_0>(_src->v())) {
          const auto &_alt = std::get<R_div2_0>(_src->v());
          _dst->v_ = R_div2_0{_alt.n};
        } else if (std::holds_alternative<R_div2_1>(_src->v())) {
          const auto &_alt = std::get<R_div2_1>(_src->v());
          _dst->v_ = R_div2_1{_alt.n};
        } else {
          const auto &_alt = std::get<R_div2_2>(_src->v());
          _dst->v_ = R_div2_2{_alt.n, _alt.p, _alt.a2,
                              _alt._res ? std::make_unique<R_div2>() : nullptr};
          auto &_dst_alt = std::get<R_div2_2>(_dst->v_);
          if (_alt._res) {
            _stack.push_back({_alt._res.get(), _dst_alt._res.get()});
          }
        }
      }
      return _out;
    }

    // CREATORS
    static R_div2 r_div2_0(unsigned int n) { return R_div2(R_div2_0{n}); }

    static R_div2 r_div2_1(unsigned int n) { return R_div2(R_div2_1{n}); }

    static R_div2 r_div2_2(unsigned int n, unsigned int p, unsigned int a2,
                           R_div2 _res) {
      return R_div2(
          R_div2_2{n, p, a2, std::make_unique<R_div2>(std::move(_res))});
    }

    // MANIPULATORS
    ~R_div2() {
      std::vector<std::unique_ptr<R_div2>> _stack{};
      _stack.reserve(8);
      auto _drain = [&](R_div2 &_node) {
        if (std::holds_alternative<R_div2_2>(_node.v_)) {
          auto &_alt = std::get<R_div2_2>(_node.v_);
          if (_alt._res) {
            _stack.push_back(std::move(_alt._res));
          }
        }
      };
      _drain(*this);
      while (!_stack.empty()) {
        auto _node = std::move(_stack.back());
        _stack.pop_back();
        if (_node) {
          _drain(*_node);
        }
      }
    }

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    template <typename T1, typename F0, typename F1, typename F2>
      requires std::is_invocable_r_v<T1, F0 &, unsigned int &> &&
               std::is_invocable_r_v<T1, F1 &, unsigned int &> &&
               std::is_invocable_r_v<T1, F2 &, unsigned int &, unsigned int &,
                                     unsigned int &, R_div2 &, T1 &>
    T1 R_div2_rec(F0 &&f, F1 &&f0, F2 &&f1, unsigned int, unsigned int) const {
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
                  (*_res0).template R_div2_rec<T1>(f, f0, f1, p0, a2));
      }
    }

    template <typename T1, typename F0, typename F1, typename F2>
      requires std::is_invocable_r_v<T1, F0 &, unsigned int &> &&
               std::is_invocable_r_v<T1, F1 &, unsigned int &> &&
               std::is_invocable_r_v<T1, F2 &, unsigned int &, unsigned int &,
                                     unsigned int &, R_div2 &, T1 &>
    T1 R_div2_rect(F0 &&f, F1 &&f0, F2 &&f1, unsigned int, unsigned int) const {
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
                  (*_res0).template R_div2_rect<T1>(f, f0, f1, p0, a2));
      }
    }
  };

  template <typename T1, typename F0, typename F1, typename F2>
    requires std::is_invocable_r_v<T1, F0 &, unsigned int &> &&
             std::is_invocable_r_v<T1, F1 &, unsigned int &> &&
             std::is_invocable_r_v<T1, F2 &, unsigned int &, unsigned int &,
                                   T1 &>
  static T1 div2_rect(F0 &&f, F1 &&f0, F2 &&f1, unsigned int n) {
    std::function<T1(unsigned int, T1)> f2 =
        [=](unsigned int _pa0, T1 _pa1) mutable { return f1(n, _pa0, _pa1); };
    T1 f3 = f0(n);
    T1 f4 = f(n);
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

  template <typename T1, typename F0, typename F1, typename F2>
    requires std::is_invocable_r_v<T1, F0 &, unsigned int &> &&
             std::is_invocable_r_v<T1, F1 &, unsigned int &> &&
             std::is_invocable_r_v<T1, F2 &, unsigned int &, unsigned int &,
                                   T1 &>
  static T1 div2_rec(F0 &&_x0, F1 &&_x1, F2 &&_x2, unsigned int _x3) {
    return div2_rect<T1>(_x0, _x1, _x2, _x3);
  }

  static R_div2 R_div2_correct(unsigned int n, unsigned int _res);

  template <typename F0>
    requires std::is_invocable_r_v<unsigned int, F0 &, List<unsigned int> &>
  static unsigned int list_sum_F(F0 &&list_sum0, const List<unsigned int> &l) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
      return 0u;
    } else {
      const auto &[a0, a1] = std::get<typename List<unsigned int>::Cons>(l.v());
      return (a0 + list_sum0(*a1));
    }
  }

  static Sig<unsigned int> list_sum_terminate(const List<unsigned int> &l);
  static unsigned int list_sum(const List<unsigned int> &l);

  struct R_list_sum {
    // TYPES
    struct R_list_sum_0 {
      List<unsigned int> l;
    };

    struct R_list_sum_1 {
      List<unsigned int> l;
      unsigned int x;
      List<unsigned int> xs;
      unsigned int a3;
      std::unique_ptr<R_list_sum> _res;
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

    R_list_sum(const R_list_sum &_other) : v_(std::move(_other.clone().v_)) {}

    R_list_sum(R_list_sum &&_other) noexcept : v_(std::move(_other.v_)) {}

    R_list_sum &operator=(const R_list_sum &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    R_list_sum &operator=(R_list_sum &&_other) noexcept {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    R_list_sum clone() const {
      R_list_sum _out{};

      struct _CloneFrame {
        const R_list_sum *_src;
        R_list_sum *_dst;
      };

      std::vector<_CloneFrame> _stack{};
      _stack.reserve(8);
      _stack.push_back({this, &_out});
      while (!_stack.empty()) {
        auto _frame = _stack.back();
        _stack.pop_back();
        const R_list_sum *_src = _frame._src;
        R_list_sum *_dst = _frame._dst;
        if (std::holds_alternative<R_list_sum_0>(_src->v())) {
          const auto &_alt = std::get<R_list_sum_0>(_src->v());
          _dst->v_ = R_list_sum_0{_alt.l.clone()};
        } else {
          const auto &_alt = std::get<R_list_sum_1>(_src->v());
          _dst->v_ = R_list_sum_1{
              _alt.l.clone(), _alt.x, _alt.xs.clone(), _alt.a3,
              _alt._res ? std::make_unique<R_list_sum>() : nullptr};
          auto &_dst_alt = std::get<R_list_sum_1>(_dst->v_);
          if (_alt._res) {
            _stack.push_back({_alt._res.get(), _dst_alt._res.get()});
          }
        }
      }
      return _out;
    }

    // CREATORS
    static R_list_sum r_list_sum_0(List<unsigned int> l) {
      return R_list_sum(R_list_sum_0{std::move(l)});
    }

    static R_list_sum r_list_sum_1(List<unsigned int> l, unsigned int x,
                                   List<unsigned int> xs, unsigned int a3,
                                   R_list_sum _res) {
      return R_list_sum(
          R_list_sum_1{std::move(l), x, std::move(xs), a3,
                       std::make_unique<R_list_sum>(std::move(_res))});
    }

    // MANIPULATORS
    ~R_list_sum() {
      std::vector<std::unique_ptr<R_list_sum>> _stack{};
      _stack.reserve(8);
      auto _drain = [&](R_list_sum &_node) {
        if (std::holds_alternative<R_list_sum_1>(_node.v_)) {
          auto &_alt = std::get<R_list_sum_1>(_node.v_);
          if (_alt._res) {
            _stack.push_back(std::move(_alt._res));
          }
        }
      };
      _drain(*this);
      while (!_stack.empty()) {
        auto _node = std::move(_stack.back());
        _stack.pop_back();
        if (_node) {
          _drain(*_node);
        }
      }
    }

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    template <typename T1, typename F0, typename F1>
      requires std::is_invocable_r_v<T1, F0 &, List<unsigned int> &> &&
               std::is_invocable_r_v<T1, F1 &, List<unsigned int> &,
                                     unsigned int &, List<unsigned int> &,
                                     unsigned int &, R_list_sum &, T1 &>
    T1 R_list_sum_rec(F0 &&f, F1 &&f0, const List<unsigned int> &,
                      unsigned int) const {
      if (std::holds_alternative<typename R_list_sum::R_list_sum_0>(
              this->v())) {
        const auto &[l0] =
            std::get<typename R_list_sum::R_list_sum_0>(this->v());
        return f(l0);
      } else {
        const auto &[l0, x0, xs0, a3, _res0] =
            std::get<typename R_list_sum::R_list_sum_1>(this->v());
        return f0(l0, x0, xs0, a3, *_res0,
                  (*_res0).template R_list_sum_rec<T1>(f, f0, xs0, a3));
      }
    }

    template <typename T1, typename F0, typename F1>
      requires std::is_invocable_r_v<T1, F0 &, List<unsigned int> &> &&
               std::is_invocable_r_v<T1, F1 &, List<unsigned int> &,
                                     unsigned int &, List<unsigned int> &,
                                     unsigned int &, R_list_sum &, T1 &>
    T1 R_list_sum_rect(F0 &&f, F1 &&f0, const List<unsigned int> &,
                       unsigned int) const {
      if (std::holds_alternative<typename R_list_sum::R_list_sum_0>(
              this->v())) {
        const auto &[l0] =
            std::get<typename R_list_sum::R_list_sum_0>(this->v());
        return f(l0);
      } else {
        const auto &[l0, x0, xs0, a3, _res0] =
            std::get<typename R_list_sum::R_list_sum_1>(this->v());
        return f0(l0, x0, xs0, a3, *_res0,
                  (*_res0).template R_list_sum_rect<T1>(f, f0, xs0, a3));
      }
    }
  };

  template <typename T1, typename F0, typename F1>
    requires std::is_invocable_r_v<T1, F0 &, List<unsigned int> &> &&
             std::is_invocable_r_v<T1, F1 &, List<unsigned int> &,
                                   unsigned int &, List<unsigned int> &, T1 &>
  static T1 list_sum_rect(F0 &&f, F1 &&f0, const List<unsigned int> &l) {
    std::function<T1(unsigned int, List<unsigned int>, T1)> f1 =
        [=](unsigned int _pa0, List<unsigned int> _pa1, T1 _pa2) mutable {
          return f0(l, _pa0, _pa1, _pa2);
        };
    T1 f2 = f(l);
    if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
      return f2;
    } else {
      const auto &[a0, a1] = std::get<typename List<unsigned int>::Cons>(l.v());
      const List<unsigned int> &a1_value = *a1;
      std::function<T1(T1)> f3 = [=](T1 _pa0) mutable {
        return f1(a0, a1_value, _pa0);
      };
      T1 hrec = list_sum_rect<T1>(f, f0, a1_value);
      return f3(hrec);
    }
  }

  template <typename T1, typename F0, typename F1>
    requires std::is_invocable_r_v<T1, F0 &, List<unsigned int> &> &&
             std::is_invocable_r_v<T1, F1 &, List<unsigned int> &,
                                   unsigned int &, List<unsigned int> &, T1 &>
  static T1 list_sum_rec(F0 &&_x0, F1 &&_x1, const List<unsigned int> &_x2) {
    return list_sum_rect<T1>(_x0, _x1, _x2);
  }

  static R_list_sum R_list_sum_correct(const List<unsigned int> &l,
                                       unsigned int _res);
  static inline const unsigned int test_div2 = div2(10u);
  static inline const unsigned int test_sum = list_sum(List<unsigned int>::cons(
      1u, List<unsigned int>::cons(
              2u, List<unsigned int>::cons(
                      3u, List<unsigned int>::cons(
                              4u, List<unsigned int>::cons(
                                      5u, List<unsigned int>::nil()))))));
};

#endif // INCLUDED_FUNCTION_VERNAC
