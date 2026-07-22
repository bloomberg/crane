#ifndef INCLUDED_STMONAD
#define INCLUDED_STMONAD

#include <algorithm>
#include <any>
#include <concepts>
#include <functional>
#include <memory>
#include <optional>
#include <string>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

using namespace std::string_literals;

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
  ~List() {
    std::vector<std::shared_ptr<List<A>>> _stack = {};
    auto _drain = [&](variant_t &_v) {
      if (auto *_alt = std::get_if<Cons>(&_v)) {
        if (_alt->l) {
          _stack.push_back(std::move(_alt->l));
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

  template <typename F0>
    requires std::is_invocable_r_v<bool, F0 &, A &>
  List<A> filter(F0 &&f) const {
    if (std::holds_alternative<typename List<A>::Nil>(this->v())) {
      return List<A>::nil();
    } else {
      const auto &[a0, a1] = std::get<typename List<A>::Cons>(this->v());
      if (f(a0)) {
        return List<A>::cons(a0, a1->filter(f));
      } else {
        return a1->filter(f);
      }
    }
  }

  uint64_t length() const {
    if (std::holds_alternative<typename List<A>::Nil>(this->v())) {
      return UINT64_C(0);
    } else {
      const auto &[a0, a1] = std::get<typename List<A>::Cons>(this->v());
      return (a1->length() + 1);
    }
  }

  List<A> app(List<A> m) const {
    if (std::holds_alternative<typename List<A>::Nil>(this->v())) {
      return m;
    } else {
      const auto &[a0, a1] = std::get<typename List<A>::Cons>(this->v());
      return List<A>::cons(a0, a1->app(std::move(m)));
    }
  }
};

template <typename Err> struct ExceptE {
  // DATA
  Err a0;

  // ACCESSORS
  ExceptE<Err> clone() const { return {a0}; }

  // CREATORS
  static ExceptE<Err> Throw_(Err a0) { return {std::move(a0)}; }
};

struct Ascii {
  // DATA
  bool a0;
  bool a1;
  bool a2;
  bool a3;
  bool a4;
  bool a5;
  bool a6;
  bool a7;

  // ACCESSORS
  Ascii clone() const { return {a0, a1, a2, a3, a4, a5, a6, a7}; }

  // CREATORS
  static Ascii ascii0(bool a0, bool a1, bool a2, bool a3, bool a4, bool a5,
                      bool a6, bool a7) {
    return {a0, a1, a2, a3, a4, a5, a6, a7};
  }
};

struct ListDef {
  static List<uint64_t> seq(uint64_t start, uint64_t len);
};

struct STMonadExamples {
  template <typename F1>
    requires std::is_invocable_r_v<List<uint64_t>, F1 &, List<uint64_t> &>
  static List<uint64_t> quicksort_fun_functional(const List<uint64_t> &l,
                                                 F1 &&quicksort_fun0);
};

struct String {
  // TYPES
  struct EmptyString {};

  struct String0 {
    Ascii a0;
    std::shared_ptr<String> a1;
  };

  using variant_t = std::variant<EmptyString, String0>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  String() {}

  explicit String(EmptyString _v) : v_(_v) {}

  explicit String(String0 _v) : v_(std::move(_v)) {}

  static String emptystring() { return String(EmptyString{}); }

  static String string0(Ascii a0, String a1) {
    return String(
        String0{std::move(a0), std::make_shared<String>(std::move(a1))});
  }

  // MANIPULATORS
  ~String() {
    std::vector<std::shared_ptr<String>> _stack = {};
    auto _drain = [&](variant_t &_v) {
      if (auto *_alt = std::get_if<String0>(&_v)) {
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

struct Err {
  // DATA
  String x;

  // ACCESSORS
  Err clone() const { return {x}; }

  // CREATORS
  static Err error(String x) { return {std::move(x)}; }
};

template <typename I, typename T>
concept Ix = requires {
  {
    I::range(std::declval<T>(), std::declval<T>())
  } -> std::convertible_to<List<T>>;
  {
    I::index(std::declval<T>(), std::declval<T>(), std::declval<T>())
  } -> std::convertible_to<std::optional<uint64_t>>;
  {
    I::rangeSize(std::declval<T>(), std::declval<T>())
  } -> std::convertible_to<uint64_t>;
  { I::toNat(std::declval<T>()) } -> std::convertible_to<uint64_t>;
  { I::fromNat(std::declval<uint64_t>()) } -> std::convertible_to<T>;
  { I::suc(std::declval<T>()) } -> std::convertible_to<T>;
  { I::sub(std::declval<T>(), std::declval<T>()) } -> std::convertible_to<T>;
  { I::max(std::declval<T>(), std::declval<T>()) } -> std::convertible_to<T>;
  { I::zero() } -> std::convertible_to<T>;
};
template <typename I, typename T>
concept STRefClass = requires {
  { I::mkSTRef(std::declval<T>()) } -> std::convertible_to<std::any>;
  { I::STRefToIx(std::declval<std::any>()) } -> std::convertible_to<T>;
};

struct STRefNat {
  // DATA
  uint64_t s;

  // ACCESSORS
  STRefNat clone() const { return {s}; }

  // CREATORS
  static STRefNat mkstref(uint64_t s) { return {s}; }

  uint64_t STRefToIxNat() const {
    const auto &[s] = *this;
    return s;
  }
};

struct STMonadTests {
  struct nat_idx {
    static List<uint64_t> range(uint64_t fp, uint64_t sp) {
      return ListDef::seq(fp, ((((UINT64_C(1) + sp) - fp) > (UINT64_C(1) + sp)
                                    ? 0
                                    : ((UINT64_C(1) + sp) - fp))));
    }

    static std::optional<uint64_t> index(uint64_t fp, uint64_t sp, uint64_t i) {
      if ((fp <= i && i <= sp)) {
        return std::make_optional<uint64_t>((((i - fp) > i ? 0 : (i - fp))));
      } else {
        return std::optional<uint64_t>();
      }
    }

    static uint64_t rangeSize(uint64_t fp, uint64_t sp) {
      return ((((UINT64_C(1) + sp) - fp) > (UINT64_C(1) + sp)
                   ? 0
                   : ((UINT64_C(1) + sp) - fp)));
    }

    static uint64_t toNat(uint64_t n) { return n; }

    static uint64_t fromNat(uint64_t n) { return n; }

    static uint64_t suc(uint64_t x) { return (x + 1); }

    static uint64_t sub(uint64_t a0, uint64_t a1) {
      return (((a0 - a1) > a0 ? 0 : (a0 - a1)));
    }

    static uint64_t max(uint64_t a0, uint64_t a1) { return std::max(a0, a1); }

    static uint64_t zero() { return UINT64_C(0); }
  };

  static_assert(Ix<nat_idx, uint64_t>);

  struct nat_stref {
    static std::any mkSTRef(uint64_t x) { return STRefNat::mkstref(x); }

    static uint64_t STRefToIx(std::any _p_a0) {
      STRefNat a0 = std::any_cast<STRefNat>(_p_a0);
      return a0.STRefToIxNat();
    }
  };

  static_assert(STRefClass<nat_stref, uint64_t>);
  static uint64_t array_simp_fixed_init();
  static std::pair<std::pair<uint64_t, uint64_t>, List<uint64_t>>
  array_simp_list();

  template <typename _tcI0, typename _tcI1>
    requires STRefClass<_tcI0, uint64_t> && Ix<_tcI1, uint64_t>
  static uint64_t fib_ST(uint64_t n) {
    if (n < UINT64_C(2)) {
      return n;
    } else {
      uint64_t x;
      x = UINT64_C(0);
      uint64_t y;
      y = UINT64_C(1);
      auto fib_loop_impl = [&](auto &, uint64_t k, uint64_t x0, uint64_t y0,
                               uint64_t, uint64_t) -> uint64_t {
        uint64_t _loop_k = std::move(k);
        while (true) {
          if (_loop_k <= 0) {
            return x0;
          } else {
            uint64_t k_ = _loop_k - 1;
            uint64_t x_ = x0;
            uint64_t y_ = y0;
            x0 = y_;
            y0 = (x_ + y_);
            _loop_k = k_;
          }
        }
      };
      auto fib_loop = [&](uint64_t k, uint64_t x0, uint64_t y0, uint64_t idx_x,
                          uint64_t idx_y) -> uint64_t {
        return fib_loop_impl(fib_loop_impl, k, x0, y0, idx_x, idx_y);
      };
      return fib_loop(n, x, y, _tcI1::zero(), _tcI1::suc(_tcI1::zero()));
    }
  }

  static uint64_t fib_fun(uint64_t n);
  static uint64_t nth(uint64_t n, const List<uint64_t> &l, uint64_t default0);

  template <typename _tcI0, typename _tcI1>
    requires STRefClass<_tcI0, uint64_t> && Ix<_tcI1, uint64_t>
  static std::pair<bool, bool> new_and_read_both_bool() {
    bool r1;
    r1 = false;
    bool r2;
    r2 = true;
    bool x1 = r1;
    bool x2 = r2;
    return std::make_pair(x1, x2);
  }

  template <typename _tcI0, typename _tcI1>
    requires STRefClass<_tcI0, uint64_t> && Ix<_tcI1, uint64_t>
  static std::pair<uint64_t, uint64_t> new_and_read_both_nat() {
    uint64_t r1;
    r1 = UINT64_C(5);
    uint64_t r2;
    r2 = UINT64_C(6);
    uint64_t x1 = r1;
    uint64_t x2 = r2;
    return std::make_pair(x1, x2);
  }

  template <typename _tcI0, typename _tcI1>
    requires STRefClass<_tcI0, uint64_t> && Ix<_tcI1, uint64_t>
  static uint64_t tree_simp_another_nat() {
    uint64_t v;
    v = UINT64_C(5);
    v = UINT64_C(6);
    uint64_t val = v;
    return val;
  }

  template <typename _tcI0, typename _tcI1>
    requires STRefClass<_tcI0, uint64_t> && Ix<_tcI1, uint64_t>
  static bool tree_simp_bool() {
    bool v;
    v = true;
    return std::move(v);
  }

  template <typename _tcI0, typename _tcI1>
    requires STRefClass<_tcI0, uint64_t> && Ix<_tcI1, uint64_t>
  static uint64_t tree_simp_nat() {
    uint64_t v;
    v = UINT64_C(5);
    return std::move(v);
  }

  static List<uint64_t> quicksort_fun(const List<uint64_t> &x);
  static List<uint64_t> quicksort_ST_mine(const List<uint64_t> &xs);
  static std::string list_to_string_helper(const List<uint64_t> &l);
  static std::string list_to_string(const List<uint64_t> &l);
  static List<uint64_t> rep_list_nat(List<uint64_t> l, uint64_t n);
  static inline const List<uint64_t> input_lst1 = List<uint64_t>::cons(
      UINT64_C(212498),
      List<uint64_t>::cons(
          UINT64_C(127),
          List<uint64_t>::cons(
              UINT64_C(5981),
              List<uint64_t>::cons(
                  UINT64_C(2749812),
                  List<uint64_t>::cons(
                      UINT64_C(74879),
                      List<uint64_t>::cons(
                          UINT64_C(126),
                          List<uint64_t>::cons(
                              UINT64_C(4),
                              List<uint64_t>::cons(
                                  UINT64_C(51),
                                  List<uint64_t>::cons(
                                      UINT64_C(2412),
                                      List<uint64_t>::cons(
                                          UINT64_C(10645),
                                          List<uint64_t>::nil()))))))))));
  static std::string test_quicksort_ST(std::monostate _x);
  static std::string test_quicksort_fun(std::monostate _x);
};

template <typename F1>
  requires std::is_invocable_r_v<List<uint64_t>, F1 &, List<uint64_t> &>
List<uint64_t>
STMonadExamples::quicksort_fun_functional(const List<uint64_t> &l,
                                          F1 &&quicksort_fun0) {
  if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
    return List<uint64_t>::nil();
  } else {
    const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
    const List<uint64_t> &a1_value = *a1;
    return quicksort_fun0(
               a1_value.filter([=](uint64_t x) mutable { return x < a0; }))
        .app(List<uint64_t>::cons(a0, List<uint64_t>::nil())
                 .app(quicksort_fun0(a1_value.filter(
                     [=](uint64_t x) mutable { return a0 <= x; }))));
  }
}

#endif // INCLUDED_STMONAD
