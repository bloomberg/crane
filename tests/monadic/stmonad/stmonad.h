#ifndef INCLUDED_STMONAD
#define INCLUDED_STMONAD

#include <algorithm>
#include <any>
#include <concepts>
#include <memory>
#include <optional>
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

  List<A> tl() const {
    if (std::holds_alternative<typename List<A>::Nil>(this->v())) {
      return List<A>::nil();
    } else {
      const auto &[a0, a1] = std::get<typename List<A>::Cons>(this->v());
      return *a1;
    }
  }

  A hd(A default0) const {
    if (std::holds_alternative<typename List<A>::Nil>(this->v())) {
      return default0;
    } else {
      const auto &[a0, a1] = std::get<typename List<A>::Cons>(this->v());
      return a0;
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
concept Ix = requires(T a0, T a1, T a2) {
  { I::range(a0, a1) } -> std::convertible_to<List<T>>;
  { I::index(a0, a1, a2) } -> std::convertible_to<std::optional<uint64_t>>;
  { I::rangeSize(a0, a1) } -> std::convertible_to<uint64_t>;
  { I::toNat(a0) } -> std::convertible_to<uint64_t>;
  { I::fromNat(a0) } -> std::convertible_to<T>;
  { I::suc(a0) } -> std::convertible_to<T>;
  { I::sub(a0, a1) } -> std::convertible_to<T>;
  { I::max(a0, a1) } -> std::convertible_to<T>;
  { I::zero() } -> std::convertible_to<T>;
};
template <typename I, typename T>
concept STRefClass = requires(T a0) {
  { I::mkSTRef(a0) } -> std::convertible_to<std::any>;
  { I::STRefToIx(a0) } -> std::convertible_to<T>;
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

template <typename _tcI0, typename _tcI1, typename T1>
std::pair<uint64_t, uint64_t> new_and_read_both_nat() {
  uint64_t r1;
  r1 = UINT64_C(5);
  uint64_t r2;
  r2 = UINT64_C(6);
  uint64_t x1 = r1;
  uint64_t x2 = r2;
  return std::make_pair(x1, x2);
}

template <typename _tcI0, typename _tcI1, typename T1>
uint64_t tree_simp_nat() {
  uint64_t v;
  v = UINT64_C(5);
  return std::move(v);
}

template <typename _tcI0, typename _tcI1, typename T1>
uint64_t tree_simp_another_nat() {
  uint64_t v;
  v = UINT64_C(5);
  v = UINT64_C(6);
  uint64_t val = v;
  return val;
}

template <typename _tcI0, typename _tcI1, typename T1>
uint64_t array_simp_fixed_init() {
  std::vector<uint64_t> *arr;
  arr = new std::remove_pointer_t<decltype(arr)>(
      _tcI1::suc(
          _tcI1::suc(_tcI1::suc(_tcI1::suc(_tcI1::suc(_tcI1::zero()))))) -
          _tcI1::zero() + 1,
      UINT64_C(5));
  uint64_t elem = (*arr)[_tcI1::suc(_tcI1::zero())];
  return elem;
}

template <typename _tcI0, typename _tcI1, typename T1>
std::pair<std::pair<uint64_t, uint64_t>, List<uint64_t>> array_simp_list() {
  std::vector<uint64_t> *arr;
  arr = new std::remove_pointer_t<decltype(arr)>(
      _tcI1::suc(_tcI1::suc(_tcI1::suc(_tcI1::zero()))) - _tcI1::zero() + 1);
  {
    auto _xs = List<uint64_t>::cons(
        UINT64_C(5),
        List<uint64_t>::cons(
            UINT64_C(4),
            List<uint64_t>::cons(
                UINT64_C(3),
                List<uint64_t>::cons(UINT64_C(2), List<uint64_t>::nil()))));
    for (size_t _i = 0; _i < arr->size(); _i++) {
      if (std::holds_alternative<
              typename std::remove_cvref_t<decltype(_xs)>::Cons>(_xs.v())) {
        auto &[_a, _l] =
            std::get<typename std::remove_cvref_t<decltype(_xs)>::Cons>(
                _xs.v_mut());
        (*arr)[_i] = _a;
        if (_l)
          _xs = *_l;
      }
    }
  };
  uint64_t elem = (*arr)[_tcI1::zero()];
  List<uint64_t> lst = [&]() {
    using _E = typename std::remove_pointer_t<
        std::remove_cvref_t<decltype(arr)>>::value_type;
    List<_E> _r = List<_E>::nil();
    for (size_t _i = arr->size(); _i > 0; _i--) {
      _r = List<_E>::cons((*arr)[_i - 1], std::move(_r));
    }
    return _r;
  }();
  return std::make_pair(std::make_pair(elem, lst.length()), lst);
}

template <typename _tcI0, typename _tcI1, typename T1>
uint64_t fibST(uint64_t n) {
  auto fibST__impl = [](auto &_self_fibST_, uint64_t n0, uint64_t x, uint64_t y,
                        const T1 &idx_x, const T1 &idx_y) -> uint64_t {
    if (n0 <= 0) {
      return x;
    } else {
      uint64_t n1 = n0 - 1;
      uint64_t x_ = x;
      uint64_t y_ = y;
      x = y_;
      y = (x_ + y_);
      return _self_fibST_(_self_fibST_, n1, x, y, idx_x, idx_y);
    }
  };
  auto fibST_ = [&](uint64_t n0, uint64_t x, uint64_t y, const T1 &idx_x,
                    const T1 &idx_y) -> uint64_t {
    return fibST__impl(fibST__impl, n0, x, y, idx_x, idx_y);
  };
  if (n <= UINT64_C(2)) {
    return n;
  } else {
    uint64_t x;
    x = UINT64_C(0);
    uint64_t y;
    y = UINT64_C(1);
    return fibST_(n, std::move(x), std::move(y), _tcI1::zero(),
                  _tcI1::suc(_tcI1::zero()));
  }
}

uint64_t fibFun(uint64_t n);

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
};

template <typename _tcI0, typename _tcI1, typename T1>
std::pair<bool, bool> new_and_read_both_bool() {
  bool r1;
  r1 = false;
  bool r2;
  r2 = true;
  bool x1 = r1;
  bool x2 = r2;
  return std::make_pair(x1, x2);
}

template <typename _tcI0, typename _tcI1, typename T1> bool tree_simp_bool() {
  bool v;
  v = true;
  return std::move(v);
}

template <typename T1> T1 list_hd(const T1 &_x0, const List<T1> &_x1) {
  return _x1.hd(_x0);
}

template <typename T1> List<T1> list_tl(const List<T1> &_x0) {
  return _x0.tl();
}

#endif // INCLUDED_STMONAD
