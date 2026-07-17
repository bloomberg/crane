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

struct Uint {
  // TYPES
  struct Nil {};

  struct D0 {
    std::shared_ptr<Uint> a0;
  };

  struct D1 {
    std::shared_ptr<Uint> a0;
  };

  struct D2 {
    std::shared_ptr<Uint> a0;
  };

  struct D3 {
    std::shared_ptr<Uint> a0;
  };

  struct D4 {
    std::shared_ptr<Uint> a0;
  };

  struct D5 {
    std::shared_ptr<Uint> a0;
  };

  struct D6 {
    std::shared_ptr<Uint> a0;
  };

  struct D7 {
    std::shared_ptr<Uint> a0;
  };

  struct D8 {
    std::shared_ptr<Uint> a0;
  };

  struct D9 {
    std::shared_ptr<Uint> a0;
  };

  using variant_t = std::variant<Nil, D0, D1, D2, D3, D4, D5, D6, D7, D8, D9>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Uint() {}

  explicit Uint(Nil _v) : v_(_v) {}

  explicit Uint(D0 _v) : v_(std::move(_v)) {}

  explicit Uint(D1 _v) : v_(std::move(_v)) {}

  explicit Uint(D2 _v) : v_(std::move(_v)) {}

  explicit Uint(D3 _v) : v_(std::move(_v)) {}

  explicit Uint(D4 _v) : v_(std::move(_v)) {}

  explicit Uint(D5 _v) : v_(std::move(_v)) {}

  explicit Uint(D6 _v) : v_(std::move(_v)) {}

  explicit Uint(D7 _v) : v_(std::move(_v)) {}

  explicit Uint(D8 _v) : v_(std::move(_v)) {}

  explicit Uint(D9 _v) : v_(std::move(_v)) {}

  static Uint nil() { return Uint(Nil{}); }

  static Uint d0(Uint a0) {
    return Uint(D0{std::make_shared<Uint>(std::move(a0))});
  }

  static Uint d1(Uint a0) {
    return Uint(D1{std::make_shared<Uint>(std::move(a0))});
  }

  static Uint d2(Uint a0) {
    return Uint(D2{std::make_shared<Uint>(std::move(a0))});
  }

  static Uint d3(Uint a0) {
    return Uint(D3{std::make_shared<Uint>(std::move(a0))});
  }

  static Uint d4(Uint a0) {
    return Uint(D4{std::make_shared<Uint>(std::move(a0))});
  }

  static Uint d5(Uint a0) {
    return Uint(D5{std::make_shared<Uint>(std::move(a0))});
  }

  static Uint d6(Uint a0) {
    return Uint(D6{std::make_shared<Uint>(std::move(a0))});
  }

  static Uint d7(Uint a0) {
    return Uint(D7{std::make_shared<Uint>(std::move(a0))});
  }

  static Uint d8(Uint a0) {
    return Uint(D8{std::make_shared<Uint>(std::move(a0))});
  }

  static Uint d9(Uint a0) {
    return Uint(D9{std::make_shared<Uint>(std::move(a0))});
  }

  // MANIPULATORS
  ~Uint() {
    std::vector<std::shared_ptr<Uint>> _stack = {};
    auto _drain = [&](variant_t &_v) {
      if (auto *_alt = std::get_if<D0>(&_v)) {
        if (_alt->a0) {
          _stack.push_back(std::move(_alt->a0));
        }
      }
      if (auto *_alt = std::get_if<D1>(&_v)) {
        if (_alt->a0) {
          _stack.push_back(std::move(_alt->a0));
        }
      }
      if (auto *_alt = std::get_if<D2>(&_v)) {
        if (_alt->a0) {
          _stack.push_back(std::move(_alt->a0));
        }
      }
      if (auto *_alt = std::get_if<D3>(&_v)) {
        if (_alt->a0) {
          _stack.push_back(std::move(_alt->a0));
        }
      }
      if (auto *_alt = std::get_if<D4>(&_v)) {
        if (_alt->a0) {
          _stack.push_back(std::move(_alt->a0));
        }
      }
      if (auto *_alt = std::get_if<D5>(&_v)) {
        if (_alt->a0) {
          _stack.push_back(std::move(_alt->a0));
        }
      }
      if (auto *_alt = std::get_if<D6>(&_v)) {
        if (_alt->a0) {
          _stack.push_back(std::move(_alt->a0));
        }
      }
      if (auto *_alt = std::get_if<D7>(&_v)) {
        if (_alt->a0) {
          _stack.push_back(std::move(_alt->a0));
        }
      }
      if (auto *_alt = std::get_if<D8>(&_v)) {
        if (_alt->a0) {
          _stack.push_back(std::move(_alt->a0));
        }
      }
      if (auto *_alt = std::get_if<D9>(&_v)) {
        if (_alt->a0) {
          _stack.push_back(std::move(_alt->a0));
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

struct Uint0 {
  // TYPES
  struct Nil0 {};

  struct D10 {
    std::shared_ptr<Uint0> a0;
  };

  struct D11 {
    std::shared_ptr<Uint0> a0;
  };

  struct D12 {
    std::shared_ptr<Uint0> a0;
  };

  struct D13 {
    std::shared_ptr<Uint0> a0;
  };

  struct D14 {
    std::shared_ptr<Uint0> a0;
  };

  struct D15 {
    std::shared_ptr<Uint0> a0;
  };

  struct D16 {
    std::shared_ptr<Uint0> a0;
  };

  struct D17 {
    std::shared_ptr<Uint0> a0;
  };

  struct D18 {
    std::shared_ptr<Uint0> a0;
  };

  struct D19 {
    std::shared_ptr<Uint0> a0;
  };

  struct Da {
    std::shared_ptr<Uint0> a0;
  };

  struct Db {
    std::shared_ptr<Uint0> a0;
  };

  struct Dc {
    std::shared_ptr<Uint0> a0;
  };

  struct Dd {
    std::shared_ptr<Uint0> a0;
  };

  struct De {
    std::shared_ptr<Uint0> a0;
  };

  struct Df {
    std::shared_ptr<Uint0> a0;
  };

  using variant_t = std::variant<Nil0, D10, D11, D12, D13, D14, D15, D16, D17,
                                 D18, D19, Da, Db, Dc, Dd, De, Df>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Uint0() {}

  explicit Uint0(Nil0 _v) : v_(_v) {}

  explicit Uint0(D10 _v) : v_(std::move(_v)) {}

  explicit Uint0(D11 _v) : v_(std::move(_v)) {}

  explicit Uint0(D12 _v) : v_(std::move(_v)) {}

  explicit Uint0(D13 _v) : v_(std::move(_v)) {}

  explicit Uint0(D14 _v) : v_(std::move(_v)) {}

  explicit Uint0(D15 _v) : v_(std::move(_v)) {}

  explicit Uint0(D16 _v) : v_(std::move(_v)) {}

  explicit Uint0(D17 _v) : v_(std::move(_v)) {}

  explicit Uint0(D18 _v) : v_(std::move(_v)) {}

  explicit Uint0(D19 _v) : v_(std::move(_v)) {}

  explicit Uint0(Da _v) : v_(std::move(_v)) {}

  explicit Uint0(Db _v) : v_(std::move(_v)) {}

  explicit Uint0(Dc _v) : v_(std::move(_v)) {}

  explicit Uint0(Dd _v) : v_(std::move(_v)) {}

  explicit Uint0(De _v) : v_(std::move(_v)) {}

  explicit Uint0(Df _v) : v_(std::move(_v)) {}

  static Uint0 nil0() { return Uint0(Nil0{}); }

  static Uint0 d10(Uint0 a0) {
    return Uint0(D10{std::make_shared<Uint0>(std::move(a0))});
  }

  static Uint0 d11(Uint0 a0) {
    return Uint0(D11{std::make_shared<Uint0>(std::move(a0))});
  }

  static Uint0 d12(Uint0 a0) {
    return Uint0(D12{std::make_shared<Uint0>(std::move(a0))});
  }

  static Uint0 d13(Uint0 a0) {
    return Uint0(D13{std::make_shared<Uint0>(std::move(a0))});
  }

  static Uint0 d14(Uint0 a0) {
    return Uint0(D14{std::make_shared<Uint0>(std::move(a0))});
  }

  static Uint0 d15(Uint0 a0) {
    return Uint0(D15{std::make_shared<Uint0>(std::move(a0))});
  }

  static Uint0 d16(Uint0 a0) {
    return Uint0(D16{std::make_shared<Uint0>(std::move(a0))});
  }

  static Uint0 d17(Uint0 a0) {
    return Uint0(D17{std::make_shared<Uint0>(std::move(a0))});
  }

  static Uint0 d18(Uint0 a0) {
    return Uint0(D18{std::make_shared<Uint0>(std::move(a0))});
  }

  static Uint0 d19(Uint0 a0) {
    return Uint0(D19{std::make_shared<Uint0>(std::move(a0))});
  }

  static Uint0 da(Uint0 a0) {
    return Uint0(Da{std::make_shared<Uint0>(std::move(a0))});
  }

  static Uint0 db(Uint0 a0) {
    return Uint0(Db{std::make_shared<Uint0>(std::move(a0))});
  }

  static Uint0 dc(Uint0 a0) {
    return Uint0(Dc{std::make_shared<Uint0>(std::move(a0))});
  }

  static Uint0 dd(Uint0 a0) {
    return Uint0(Dd{std::make_shared<Uint0>(std::move(a0))});
  }

  static Uint0 de(Uint0 a0) {
    return Uint0(De{std::make_shared<Uint0>(std::move(a0))});
  }

  static Uint0 df(Uint0 a0) {
    return Uint0(Df{std::make_shared<Uint0>(std::move(a0))});
  }

  // MANIPULATORS
  ~Uint0() {
    std::vector<std::shared_ptr<Uint0>> _stack = {};
    auto _drain = [&](variant_t &_v) {
      if (auto *_alt = std::get_if<D10>(&_v)) {
        if (_alt->a0) {
          _stack.push_back(std::move(_alt->a0));
        }
      }
      if (auto *_alt = std::get_if<D11>(&_v)) {
        if (_alt->a0) {
          _stack.push_back(std::move(_alt->a0));
        }
      }
      if (auto *_alt = std::get_if<D12>(&_v)) {
        if (_alt->a0) {
          _stack.push_back(std::move(_alt->a0));
        }
      }
      if (auto *_alt = std::get_if<D13>(&_v)) {
        if (_alt->a0) {
          _stack.push_back(std::move(_alt->a0));
        }
      }
      if (auto *_alt = std::get_if<D14>(&_v)) {
        if (_alt->a0) {
          _stack.push_back(std::move(_alt->a0));
        }
      }
      if (auto *_alt = std::get_if<D15>(&_v)) {
        if (_alt->a0) {
          _stack.push_back(std::move(_alt->a0));
        }
      }
      if (auto *_alt = std::get_if<D16>(&_v)) {
        if (_alt->a0) {
          _stack.push_back(std::move(_alt->a0));
        }
      }
      if (auto *_alt = std::get_if<D17>(&_v)) {
        if (_alt->a0) {
          _stack.push_back(std::move(_alt->a0));
        }
      }
      if (auto *_alt = std::get_if<D18>(&_v)) {
        if (_alt->a0) {
          _stack.push_back(std::move(_alt->a0));
        }
      }
      if (auto *_alt = std::get_if<D19>(&_v)) {
        if (_alt->a0) {
          _stack.push_back(std::move(_alt->a0));
        }
      }
      if (auto *_alt = std::get_if<Da>(&_v)) {
        if (_alt->a0) {
          _stack.push_back(std::move(_alt->a0));
        }
      }
      if (auto *_alt = std::get_if<Db>(&_v)) {
        if (_alt->a0) {
          _stack.push_back(std::move(_alt->a0));
        }
      }
      if (auto *_alt = std::get_if<Dc>(&_v)) {
        if (_alt->a0) {
          _stack.push_back(std::move(_alt->a0));
        }
      }
      if (auto *_alt = std::get_if<Dd>(&_v)) {
        if (_alt->a0) {
          _stack.push_back(std::move(_alt->a0));
        }
      }
      if (auto *_alt = std::get_if<De>(&_v)) {
        if (_alt->a0) {
          _stack.push_back(std::move(_alt->a0));
        }
      }
      if (auto *_alt = std::get_if<Df>(&_v)) {
        if (_alt->a0) {
          _stack.push_back(std::move(_alt->a0));
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

struct Uint1 {
  // TYPES
  struct UIntDecimal {
    Uint u;
  };

  struct UIntHexadecimal {
    Uint0 u;
  };

  using variant_t = std::variant<UIntDecimal, UIntHexadecimal>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Uint1() {}

  explicit Uint1(UIntDecimal _v) : v_(std::move(_v)) {}

  explicit Uint1(UIntHexadecimal _v) : v_(std::move(_v)) {}

  static Uint1 uintdecimal(Uint u) { return Uint1(UIntDecimal{std::move(u)}); }

  static Uint1 uinthexadecimal(Uint0 u) {
    return Uint1(UIntHexadecimal{std::move(u)});
  }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
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

struct Nat {
  static uint64_t tail_add(uint64_t n, uint64_t m);
  static uint64_t tail_addmul(uint64_t r, uint64_t n, uint64_t m);
  static uint64_t tail_mul(uint64_t n, uint64_t m);
  static uint64_t of_uint_acc(const Uint &d, uint64_t acc);
  static uint64_t of_uint(const Uint &d);
  static uint64_t of_hex_uint_acc(const Uint0 &d, uint64_t acc);
  static uint64_t of_hex_uint(const Uint0 &d);
  static uint64_t of_num_uint(const Uint1 &d);
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

  template <typename _tcI0, typename _tcI1> static uint64_t fib_ST(uint64_t n) {
    if (n < UINT64_C(2)) {
      return n;
    } else {
      uint64_t x;
      x = UINT64_C(0);
      uint64_t y;
      y = UINT64_C(1);
      auto fib_loop_impl = [](auto &_self_fib_loop, uint64_t k, uint64_t x0,
                              uint64_t y0, uint64_t idx_x,
                              uint64_t idx_y) -> uint64_t {
        if (k <= 0) {
          return x0;
        } else {
          uint64_t k_ = k - 1;
          uint64_t x_ = x0;
          uint64_t y_ = y0;
          x0 = y_;
          y0 = (x_ + y_);
          return _self_fib_loop(_self_fib_loop, k_, x0, y0, idx_x, idx_y);
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
  static uint64_t tree_simp_another_nat() {
    uint64_t v;
    v = UINT64_C(5);
    v = UINT64_C(6);
    uint64_t val = v;
    return val;
  }

  template <typename _tcI0, typename _tcI1> static bool tree_simp_bool() {
    bool v;
    v = true;
    return std::move(v);
  }

  template <typename _tcI0, typename _tcI1> static uint64_t tree_simp_nat() {
    uint64_t v;
    v = UINT64_C(5);
    return std::move(v);
  }

  static List<uint64_t> quicksort_fun(const List<uint64_t> &x);
  static List<uint64_t> quicksort_ST_mine(const List<uint64_t> &xs);
  static std::string list_to_string_helper(const List<uint64_t> &l);
  static std::string list_to_string(const List<uint64_t> &l);
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
                                      List<uint64_t>::nil())))))))));
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
