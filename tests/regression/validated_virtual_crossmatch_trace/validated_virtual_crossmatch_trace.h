#ifndef INCLUDED_VALIDATED_VIRTUAL_CROSSMATCH_TRACE
#define INCLUDED_VALIDATED_VIRTUAL_CROSSMATCH_TRACE

#include <algorithm>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

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
  inline variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }

  template <MapsTo<bool, t_A> F0>
  __attribute__((pure)) bool existsb(F0 &&f) const {
    auto &&_sv = *(this);
    if (std::holds_alternative<typename List<t_A>::Nil>(_sv.v())) {
      return false;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<t_A>::Cons>(_sv.v());
      return (f(d_a0) || (*(d_a1)).existsb(f));
    }
  }

  template <typename T1, MapsTo<T1, T1, t_A> F0>
  T1 fold_left(F0 &&f, const T1 a0) const {
    auto &&_sv = *(this);
    if (std::holds_alternative<typename List<t_A>::Nil>(_sv.v())) {
      return a0;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<t_A>::Cons>(_sv.v());
      return (*(d_a1)).template fold_left<T1>(f, f(a0, d_a0));
    }
  }

  template <typename T1, MapsTo<List<T1>, t_A> F0>
  __attribute__((pure)) List<T1> flat_map(F0 &&f) const {
    auto &&_sv = *(this);
    if (std::holds_alternative<typename List<t_A>::Nil>(_sv.v())) {
      return List<T1>::nil();
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<t_A>::Cons>(_sv.v());
      return f(d_a0).app((*(d_a1)).template flat_map<T1>(f));
    }
  }

  __attribute__((pure)) unsigned int length() const {
    auto &&_sv = *(this);
    if (std::holds_alternative<typename List<t_A>::Nil>(_sv.v())) {
      return 0u;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<t_A>::Cons>(_sv.v());
      return ((*(d_a1)).length() + 1);
    }
  }

  __attribute__((pure)) List<t_A> app(List<t_A> m) const {
    auto &&_sv = *(this);
    if (std::holds_alternative<typename List<t_A>::Nil>(_sv.v())) {
      return m;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<t_A>::Cons>(_sv.v());
      return List<t_A>::cons(d_a0, (*(d_a1)).app(std::move(m)));
    }
  }
};

struct Uint {
  // TYPES
  struct Nil {};

  struct D0 {
    std::unique_ptr<Uint> d_a0;
  };

  struct D1 {
    std::unique_ptr<Uint> d_a0;
  };

  struct D2 {
    std::unique_ptr<Uint> d_a0;
  };

  struct D3 {
    std::unique_ptr<Uint> d_a0;
  };

  struct D4 {
    std::unique_ptr<Uint> d_a0;
  };

  struct D5 {
    std::unique_ptr<Uint> d_a0;
  };

  struct D6 {
    std::unique_ptr<Uint> d_a0;
  };

  struct D7 {
    std::unique_ptr<Uint> d_a0;
  };

  struct D8 {
    std::unique_ptr<Uint> d_a0;
  };

  struct D9 {
    std::unique_ptr<Uint> d_a0;
  };

  using variant_t = std::variant<Nil, D0, D1, D2, D3, D4, D5, D6, D7, D8, D9>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  Uint() {}

  explicit Uint(Nil _v) : d_v_(_v) {}

  explicit Uint(D0 _v) : d_v_(std::move(_v)) {}

  explicit Uint(D1 _v) : d_v_(std::move(_v)) {}

  explicit Uint(D2 _v) : d_v_(std::move(_v)) {}

  explicit Uint(D3 _v) : d_v_(std::move(_v)) {}

  explicit Uint(D4 _v) : d_v_(std::move(_v)) {}

  explicit Uint(D5 _v) : d_v_(std::move(_v)) {}

  explicit Uint(D6 _v) : d_v_(std::move(_v)) {}

  explicit Uint(D7 _v) : d_v_(std::move(_v)) {}

  explicit Uint(D8 _v) : d_v_(std::move(_v)) {}

  explicit Uint(D9 _v) : d_v_(std::move(_v)) {}

  Uint(const Uint &_other) : d_v_(std::move(_other.clone().d_v_)) {}

  Uint(Uint &&_other) : d_v_(std::move(_other.d_v_)) {}

  Uint &operator=(const Uint &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  Uint &operator=(Uint &&_other) {
    d_v_ = std::move(_other.d_v_);
    return *this;
  }

  // ACCESSORS
  __attribute__((pure)) Uint clone() const {
    auto &&_sv = *(this);
    if (std::holds_alternative<Nil>(_sv.v())) {
      return Uint(Nil{});
    } else if (std::holds_alternative<D0>(_sv.v())) {
      const auto &[d_a0] = std::get<D0>(_sv.v());
      return Uint(D0{d_a0 ? std::make_unique<Uint>(d_a0->clone()) : nullptr});
    } else if (std::holds_alternative<D1>(_sv.v())) {
      const auto &[d_a0] = std::get<D1>(_sv.v());
      return Uint(D1{d_a0 ? std::make_unique<Uint>(d_a0->clone()) : nullptr});
    } else if (std::holds_alternative<D2>(_sv.v())) {
      const auto &[d_a0] = std::get<D2>(_sv.v());
      return Uint(D2{d_a0 ? std::make_unique<Uint>(d_a0->clone()) : nullptr});
    } else if (std::holds_alternative<D3>(_sv.v())) {
      const auto &[d_a0] = std::get<D3>(_sv.v());
      return Uint(D3{d_a0 ? std::make_unique<Uint>(d_a0->clone()) : nullptr});
    } else if (std::holds_alternative<D4>(_sv.v())) {
      const auto &[d_a0] = std::get<D4>(_sv.v());
      return Uint(D4{d_a0 ? std::make_unique<Uint>(d_a0->clone()) : nullptr});
    } else if (std::holds_alternative<D5>(_sv.v())) {
      const auto &[d_a0] = std::get<D5>(_sv.v());
      return Uint(D5{d_a0 ? std::make_unique<Uint>(d_a0->clone()) : nullptr});
    } else if (std::holds_alternative<D6>(_sv.v())) {
      const auto &[d_a0] = std::get<D6>(_sv.v());
      return Uint(D6{d_a0 ? std::make_unique<Uint>(d_a0->clone()) : nullptr});
    } else if (std::holds_alternative<D7>(_sv.v())) {
      const auto &[d_a0] = std::get<D7>(_sv.v());
      return Uint(D7{d_a0 ? std::make_unique<Uint>(d_a0->clone()) : nullptr});
    } else if (std::holds_alternative<D8>(_sv.v())) {
      const auto &[d_a0] = std::get<D8>(_sv.v());
      return Uint(D8{d_a0 ? std::make_unique<Uint>(d_a0->clone()) : nullptr});
    } else {
      const auto &[d_a0] = std::get<D9>(_sv.v());
      return Uint(D9{d_a0 ? std::make_unique<Uint>(d_a0->clone()) : nullptr});
    }
  }

  // CREATORS
  __attribute__((pure)) static Uint nil() { return Uint(Nil{}); }

  __attribute__((pure)) static Uint d0(Uint a0) {
    return Uint(D0{std::make_unique<Uint>(std::move(a0))});
  }

  __attribute__((pure)) static Uint d1(Uint a0) {
    return Uint(D1{std::make_unique<Uint>(std::move(a0))});
  }

  __attribute__((pure)) static Uint d2(Uint a0) {
    return Uint(D2{std::make_unique<Uint>(std::move(a0))});
  }

  __attribute__((pure)) static Uint d3(Uint a0) {
    return Uint(D3{std::make_unique<Uint>(std::move(a0))});
  }

  __attribute__((pure)) static Uint d4(Uint a0) {
    return Uint(D4{std::make_unique<Uint>(std::move(a0))});
  }

  __attribute__((pure)) static Uint d5(Uint a0) {
    return Uint(D5{std::make_unique<Uint>(std::move(a0))});
  }

  __attribute__((pure)) static Uint d6(Uint a0) {
    return Uint(D6{std::make_unique<Uint>(std::move(a0))});
  }

  __attribute__((pure)) static Uint d7(Uint a0) {
    return Uint(D7{std::make_unique<Uint>(std::move(a0))});
  }

  __attribute__((pure)) static Uint d8(Uint a0) {
    return Uint(D8{std::make_unique<Uint>(std::move(a0))});
  }

  __attribute__((pure)) static Uint d9(Uint a0) {
    return Uint(D9{std::make_unique<Uint>(std::move(a0))});
  }

  // MANIPULATORS
  inline variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
};

struct Uint0 {
  // TYPES
  struct Nil0 {};

  struct D10 {
    std::unique_ptr<Uint0> d_a0;
  };

  struct D11 {
    std::unique_ptr<Uint0> d_a0;
  };

  struct D12 {
    std::unique_ptr<Uint0> d_a0;
  };

  struct D13 {
    std::unique_ptr<Uint0> d_a0;
  };

  struct D14 {
    std::unique_ptr<Uint0> d_a0;
  };

  struct D15 {
    std::unique_ptr<Uint0> d_a0;
  };

  struct D16 {
    std::unique_ptr<Uint0> d_a0;
  };

  struct D17 {
    std::unique_ptr<Uint0> d_a0;
  };

  struct D18 {
    std::unique_ptr<Uint0> d_a0;
  };

  struct D19 {
    std::unique_ptr<Uint0> d_a0;
  };

  struct Da {
    std::unique_ptr<Uint0> d_a0;
  };

  struct Db {
    std::unique_ptr<Uint0> d_a0;
  };

  struct Dc {
    std::unique_ptr<Uint0> d_a0;
  };

  struct Dd {
    std::unique_ptr<Uint0> d_a0;
  };

  struct De {
    std::unique_ptr<Uint0> d_a0;
  };

  struct Df {
    std::unique_ptr<Uint0> d_a0;
  };

  using variant_t = std::variant<Nil0, D10, D11, D12, D13, D14, D15, D16, D17,
                                 D18, D19, Da, Db, Dc, Dd, De, Df>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  Uint0() {}

  explicit Uint0(Nil0 _v) : d_v_(_v) {}

  explicit Uint0(D10 _v) : d_v_(std::move(_v)) {}

  explicit Uint0(D11 _v) : d_v_(std::move(_v)) {}

  explicit Uint0(D12 _v) : d_v_(std::move(_v)) {}

  explicit Uint0(D13 _v) : d_v_(std::move(_v)) {}

  explicit Uint0(D14 _v) : d_v_(std::move(_v)) {}

  explicit Uint0(D15 _v) : d_v_(std::move(_v)) {}

  explicit Uint0(D16 _v) : d_v_(std::move(_v)) {}

  explicit Uint0(D17 _v) : d_v_(std::move(_v)) {}

  explicit Uint0(D18 _v) : d_v_(std::move(_v)) {}

  explicit Uint0(D19 _v) : d_v_(std::move(_v)) {}

  explicit Uint0(Da _v) : d_v_(std::move(_v)) {}

  explicit Uint0(Db _v) : d_v_(std::move(_v)) {}

  explicit Uint0(Dc _v) : d_v_(std::move(_v)) {}

  explicit Uint0(Dd _v) : d_v_(std::move(_v)) {}

  explicit Uint0(De _v) : d_v_(std::move(_v)) {}

  explicit Uint0(Df _v) : d_v_(std::move(_v)) {}

  Uint0(const Uint0 &_other) : d_v_(std::move(_other.clone().d_v_)) {}

  Uint0(Uint0 &&_other) : d_v_(std::move(_other.d_v_)) {}

  Uint0 &operator=(const Uint0 &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  Uint0 &operator=(Uint0 &&_other) {
    d_v_ = std::move(_other.d_v_);
    return *this;
  }

  // ACCESSORS
  __attribute__((pure)) Uint0 clone() const {
    auto &&_sv = *(this);
    if (std::holds_alternative<Nil0>(_sv.v())) {
      return Uint0(Nil0{});
    } else if (std::holds_alternative<D10>(_sv.v())) {
      const auto &[d_a0] = std::get<D10>(_sv.v());
      return Uint0(
          D10{d_a0 ? std::make_unique<Uint0>(d_a0->clone()) : nullptr});
    } else if (std::holds_alternative<D11>(_sv.v())) {
      const auto &[d_a0] = std::get<D11>(_sv.v());
      return Uint0(
          D11{d_a0 ? std::make_unique<Uint0>(d_a0->clone()) : nullptr});
    } else if (std::holds_alternative<D12>(_sv.v())) {
      const auto &[d_a0] = std::get<D12>(_sv.v());
      return Uint0(
          D12{d_a0 ? std::make_unique<Uint0>(d_a0->clone()) : nullptr});
    } else if (std::holds_alternative<D13>(_sv.v())) {
      const auto &[d_a0] = std::get<D13>(_sv.v());
      return Uint0(
          D13{d_a0 ? std::make_unique<Uint0>(d_a0->clone()) : nullptr});
    } else if (std::holds_alternative<D14>(_sv.v())) {
      const auto &[d_a0] = std::get<D14>(_sv.v());
      return Uint0(
          D14{d_a0 ? std::make_unique<Uint0>(d_a0->clone()) : nullptr});
    } else if (std::holds_alternative<D15>(_sv.v())) {
      const auto &[d_a0] = std::get<D15>(_sv.v());
      return Uint0(
          D15{d_a0 ? std::make_unique<Uint0>(d_a0->clone()) : nullptr});
    } else if (std::holds_alternative<D16>(_sv.v())) {
      const auto &[d_a0] = std::get<D16>(_sv.v());
      return Uint0(
          D16{d_a0 ? std::make_unique<Uint0>(d_a0->clone()) : nullptr});
    } else if (std::holds_alternative<D17>(_sv.v())) {
      const auto &[d_a0] = std::get<D17>(_sv.v());
      return Uint0(
          D17{d_a0 ? std::make_unique<Uint0>(d_a0->clone()) : nullptr});
    } else if (std::holds_alternative<D18>(_sv.v())) {
      const auto &[d_a0] = std::get<D18>(_sv.v());
      return Uint0(
          D18{d_a0 ? std::make_unique<Uint0>(d_a0->clone()) : nullptr});
    } else if (std::holds_alternative<D19>(_sv.v())) {
      const auto &[d_a0] = std::get<D19>(_sv.v());
      return Uint0(
          D19{d_a0 ? std::make_unique<Uint0>(d_a0->clone()) : nullptr});
    } else if (std::holds_alternative<Da>(_sv.v())) {
      const auto &[d_a0] = std::get<Da>(_sv.v());
      return Uint0(Da{d_a0 ? std::make_unique<Uint0>(d_a0->clone()) : nullptr});
    } else if (std::holds_alternative<Db>(_sv.v())) {
      const auto &[d_a0] = std::get<Db>(_sv.v());
      return Uint0(Db{d_a0 ? std::make_unique<Uint0>(d_a0->clone()) : nullptr});
    } else if (std::holds_alternative<Dc>(_sv.v())) {
      const auto &[d_a0] = std::get<Dc>(_sv.v());
      return Uint0(Dc{d_a0 ? std::make_unique<Uint0>(d_a0->clone()) : nullptr});
    } else if (std::holds_alternative<Dd>(_sv.v())) {
      const auto &[d_a0] = std::get<Dd>(_sv.v());
      return Uint0(Dd{d_a0 ? std::make_unique<Uint0>(d_a0->clone()) : nullptr});
    } else if (std::holds_alternative<De>(_sv.v())) {
      const auto &[d_a0] = std::get<De>(_sv.v());
      return Uint0(De{d_a0 ? std::make_unique<Uint0>(d_a0->clone()) : nullptr});
    } else {
      const auto &[d_a0] = std::get<Df>(_sv.v());
      return Uint0(Df{d_a0 ? std::make_unique<Uint0>(d_a0->clone()) : nullptr});
    }
  }

  // CREATORS
  __attribute__((pure)) static Uint0 nil0() { return Uint0(Nil0{}); }

  __attribute__((pure)) static Uint0 d10(Uint0 a0) {
    return Uint0(D10{std::make_unique<Uint0>(std::move(a0))});
  }

  __attribute__((pure)) static Uint0 d11(Uint0 a0) {
    return Uint0(D11{std::make_unique<Uint0>(std::move(a0))});
  }

  __attribute__((pure)) static Uint0 d12(Uint0 a0) {
    return Uint0(D12{std::make_unique<Uint0>(std::move(a0))});
  }

  __attribute__((pure)) static Uint0 d13(Uint0 a0) {
    return Uint0(D13{std::make_unique<Uint0>(std::move(a0))});
  }

  __attribute__((pure)) static Uint0 d14(Uint0 a0) {
    return Uint0(D14{std::make_unique<Uint0>(std::move(a0))});
  }

  __attribute__((pure)) static Uint0 d15(Uint0 a0) {
    return Uint0(D15{std::make_unique<Uint0>(std::move(a0))});
  }

  __attribute__((pure)) static Uint0 d16(Uint0 a0) {
    return Uint0(D16{std::make_unique<Uint0>(std::move(a0))});
  }

  __attribute__((pure)) static Uint0 d17(Uint0 a0) {
    return Uint0(D17{std::make_unique<Uint0>(std::move(a0))});
  }

  __attribute__((pure)) static Uint0 d18(Uint0 a0) {
    return Uint0(D18{std::make_unique<Uint0>(std::move(a0))});
  }

  __attribute__((pure)) static Uint0 d19(Uint0 a0) {
    return Uint0(D19{std::make_unique<Uint0>(std::move(a0))});
  }

  __attribute__((pure)) static Uint0 da(Uint0 a0) {
    return Uint0(Da{std::make_unique<Uint0>(std::move(a0))});
  }

  __attribute__((pure)) static Uint0 db(Uint0 a0) {
    return Uint0(Db{std::make_unique<Uint0>(std::move(a0))});
  }

  __attribute__((pure)) static Uint0 dc(Uint0 a0) {
    return Uint0(Dc{std::make_unique<Uint0>(std::move(a0))});
  }

  __attribute__((pure)) static Uint0 dd(Uint0 a0) {
    return Uint0(Dd{std::make_unique<Uint0>(std::move(a0))});
  }

  __attribute__((pure)) static Uint0 de(Uint0 a0) {
    return Uint0(De{std::make_unique<Uint0>(std::move(a0))});
  }

  __attribute__((pure)) static Uint0 df(Uint0 a0) {
    return Uint0(Df{std::make_unique<Uint0>(std::move(a0))});
  }

  // MANIPULATORS
  inline variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
};

struct PeanoNat {
  __attribute__((pure)) static bool eq_dec(const unsigned int &n,
                                           const unsigned int &m);
};

struct Bool {
  __attribute__((pure)) static bool bool_dec(const bool &b1, const bool &b2);
};

struct Uint1 {
  // TYPES
  struct UIntDecimal {
    Uint d_u;
  };

  struct UIntHexadecimal {
    Uint0 d_u;
  };

  using variant_t = std::variant<UIntDecimal, UIntHexadecimal>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  Uint1() {}

  explicit Uint1(UIntDecimal _v) : d_v_(std::move(_v)) {}

  explicit Uint1(UIntHexadecimal _v) : d_v_(std::move(_v)) {}

  Uint1(const Uint1 &_other) : d_v_(std::move(_other.clone().d_v_)) {}

  Uint1(Uint1 &&_other) : d_v_(std::move(_other.d_v_)) {}

  Uint1 &operator=(const Uint1 &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  Uint1 &operator=(Uint1 &&_other) {
    d_v_ = std::move(_other.d_v_);
    return *this;
  }

  // ACCESSORS
  __attribute__((pure)) Uint1 clone() const {
    auto &&_sv = *(this);
    if (std::holds_alternative<UIntDecimal>(_sv.v())) {
      const auto &[d_u] = std::get<UIntDecimal>(_sv.v());
      return Uint1(UIntDecimal{d_u.clone()});
    } else {
      const auto &[d_u] = std::get<UIntHexadecimal>(_sv.v());
      return Uint1(UIntHexadecimal{d_u.clone()});
    }
  }

  // CREATORS
  __attribute__((pure)) static Uint1 uintdecimal(Uint u) {
    return Uint1(UIntDecimal{std::move(u)});
  }

  __attribute__((pure)) static Uint1 uinthexadecimal(Uint0 u) {
    return Uint1(UIntHexadecimal{std::move(u)});
  }

  // MANIPULATORS
  inline variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
};

struct Nat {
  __attribute__((pure)) static unsigned int tail_add(const unsigned int &n,
                                                     unsigned int m);
  __attribute__((pure)) static unsigned int
  tail_addmul(unsigned int r, const unsigned int &n, const unsigned int &m);
  __attribute__((pure)) static unsigned int tail_mul(const unsigned int &n,
                                                     const unsigned int &m);
  __attribute__((pure)) static unsigned int of_uint_acc(const Uint &d,
                                                        unsigned int acc);
  __attribute__((pure)) static unsigned int of_uint(const Uint &d);
  __attribute__((pure)) static unsigned int of_hex_uint_acc(const Uint0 &d,
                                                            unsigned int acc);
  __attribute__((pure)) static unsigned int of_hex_uint(const Uint0 &d);
  __attribute__((pure)) static unsigned int of_num_uint(const Uint1 &d);
};

struct ValidatedVirtualCrossmatchTraceCase {
  enum class HLALocus { e_LOCUS_A, e_LOCUS_B, e_LOCUS_DR };

  template <typename T1>
  static T1 HLALocus_rect(const T1 f, const T1 f0, const T1 f1,
                          const HLALocus h) {
    switch (h) {
    case HLALocus::e_LOCUS_A: {
      return f;
    }
    case HLALocus::e_LOCUS_B: {
      return f0;
    }
    case HLALocus::e_LOCUS_DR: {
      return f1;
    }
    default:
      std::unreachable();
    }
  }

  template <typename T1>
  static T1 HLALocus_rec(const T1 f, const T1 f0, const T1 f1,
                         const HLALocus h) {
    switch (h) {
    case HLALocus::e_LOCUS_A: {
      return f;
    }
    case HLALocus::e_LOCUS_B: {
      return f0;
    }
    case HLALocus::e_LOCUS_DR: {
      return f1;
    }
    default:
      std::unreachable();
    }
  }

  __attribute__((pure)) static bool hla_locus_eq_dec(const HLALocus x,
                                                     const HLALocus y);

  struct HLAAllele {
    HLALocus hla_locus;
    unsigned int hla_group;

    // ACCESSORS
    __attribute__((pure)) HLAAllele clone() const {
      return HLAAllele{(*(this)).hla_locus, (*(this)).hla_group};
    }
  };

  __attribute__((pure)) static bool hla_allele_eq_dec(const HLAAllele &x,
                                                      const HLAAllele &y);
  __attribute__((pure)) static bool hla_allele_eqb(const HLAAllele &x,
                                                   const HLAAllele &y);

  struct HLATyping {
    List<HLAAllele> hla_typed_alleles;

    // ACCESSORS
    __attribute__((pure)) HLATyping clone() const {
      return HLATyping{(*(this)).hla_typed_alleles.clone()};
    }
  };

  struct HLAEpitope {
    unsigned int epitope_id;
    HLALocus epitope_locus;
    bool epitope_immunogenic;

    // ACCESSORS
    __attribute__((pure)) HLAEpitope clone() const {
      return HLAEpitope{(*(this)).epitope_id, (*(this)).epitope_locus,
                        (*(this)).epitope_immunogenic};
    }
  };

  __attribute__((pure)) static bool epitope_eq_dec(const HLAEpitope &x,
                                                   const HLAEpitope &y);
  __attribute__((pure)) static bool epitope_eqb(const HLAEpitope &x,
                                                const HLAEpitope &y);
  static inline const HLAEpitope eplet_62GE =
      HLAEpitope{62u, HLALocus::e_LOCUS_A, true};
  static inline const HLAEpitope eplet_65QIA =
      HLAEpitope{65u, HLALocus::e_LOCUS_A, true};
  static inline const HLAEpitope eplet_142T =
      HLAEpitope{142u, HLALocus::e_LOCUS_B, true};
  static inline const HLAEpitope eplet_77N =
      HLAEpitope{77u, HLALocus::e_LOCUS_DR, true};
  __attribute__((pure)) static List<HLAEpitope>
  allele_epitopes(const HLAAllele &a);
  __attribute__((pure)) static List<HLAEpitope>
  typing_epitopes(const HLATyping &t);
  __attribute__((pure)) static List<HLAEpitope>
  epitope_dedup(const List<HLAEpitope> &l);

  struct EpitopeAntibody {
    HLAEpitope ab_epitope;
    unsigned int ab_mfi;
    bool ab_complement_fixing;

    // ACCESSORS
    __attribute__((pure)) EpitopeAntibody clone() const {
      return EpitopeAntibody{(*(this)).ab_epitope.clone(), (*(this)).ab_mfi,
                             (*(this)).ab_complement_fixing};
    }
  };

  struct VirtualXMProfile {
    List<EpitopeAntibody> vxm_epitope_abs;
    unsigned int vxm_current_pra;
    unsigned int vxm_peak_pra;
    unsigned int vxm_sensitization_events;

    // ACCESSORS
    __attribute__((pure)) VirtualXMProfile clone() const {
      return VirtualXMProfile{(*(this)).vxm_epitope_abs.clone(),
                              (*(this)).vxm_current_pra, (*(this)).vxm_peak_pra,
                              (*(this)).vxm_sensitization_events};
    }
  };

  struct MFIThresholdConfig {
    unsigned int mfi_cfg_negative;
    unsigned int mfi_cfg_weak_positive;
    unsigned int mfi_cfg_moderate;
    unsigned int mfi_cfg_strong;
    unsigned int mfi_cfg_lab_id;
    bool mfi_cfg_validated;

    // ACCESSORS
    __attribute__((pure)) MFIThresholdConfig clone() const {
      return MFIThresholdConfig{
          (*(this)).mfi_cfg_negative, (*(this)).mfi_cfg_weak_positive,
          (*(this)).mfi_cfg_moderate, (*(this)).mfi_cfg_strong,
          (*(this)).mfi_cfg_lab_id,   (*(this)).mfi_cfg_validated};
    }
  };

  __attribute__((pure)) static bool
  mfi_config_valid(const MFIThresholdConfig &cfg);
  static inline const MFIThresholdConfig example_luminex_thresholds =
      MFIThresholdConfig{1000u, 3000u, 8000u, 12000u, 1u, true};

  struct ValidatedMFIConfig {
    MFIThresholdConfig vmc_config;

    // ACCESSORS
    __attribute__((pure)) ValidatedMFIConfig clone() const {
      return ValidatedMFIConfig{(*(this)).vmc_config.clone()};
    }
  };

  static inline const ValidatedMFIConfig validated_luminex =
      ValidatedMFIConfig{example_luminex_thresholds};
  enum class MFIStrength {
    e_MFI_NEGATIVE,
    e_MFI_WEAKPOSITIVE,
    e_MFI_MODERATE,
    e_MFI_STRONG,
    e_MFI_VERYSTRONG
  };

  template <typename T1>
  static T1 MFIStrength_rect(const T1 f, const T1 f0, const T1 f1, const T1 f2,
                             const T1 f3, const MFIStrength m) {
    switch (m) {
    case MFIStrength::e_MFI_NEGATIVE: {
      return f;
    }
    case MFIStrength::e_MFI_WEAKPOSITIVE: {
      return f0;
    }
    case MFIStrength::e_MFI_MODERATE: {
      return f1;
    }
    case MFIStrength::e_MFI_STRONG: {
      return f2;
    }
    case MFIStrength::e_MFI_VERYSTRONG: {
      return f3;
    }
    default:
      std::unreachable();
    }
  }

  template <typename T1>
  static T1 MFIStrength_rec(const T1 f, const T1 f0, const T1 f1, const T1 f2,
                            const T1 f3, const MFIStrength m) {
    switch (m) {
    case MFIStrength::e_MFI_NEGATIVE: {
      return f;
    }
    case MFIStrength::e_MFI_WEAKPOSITIVE: {
      return f0;
    }
    case MFIStrength::e_MFI_MODERATE: {
      return f1;
    }
    case MFIStrength::e_MFI_STRONG: {
      return f2;
    }
    case MFIStrength::e_MFI_VERYSTRONG: {
      return f3;
    }
    default:
      std::unreachable();
    }
  }

  __attribute__((pure)) static MFIStrength
  classify_mfi_with_config(const MFIThresholdConfig &cfg,
                           const unsigned int &mfi);
  __attribute__((pure)) static MFIStrength
  classify_mfi_safe(const ValidatedMFIConfig &vcfg, const unsigned int &mfi);
  static inline const unsigned int mfi_negative_threshold = 1000u;
  __attribute__((pure)) static unsigned int
  max_dsa_mfi(const VirtualXMProfile &recipient, const HLATyping &donor);
  __attribute__((pure)) static bool
  has_complement_fixing_dsa(const VirtualXMProfile &recipient,
                            const HLATyping &donor);
  enum class VirtualXMResult {
    e_VXM_NEGATIVE,
    e_VXM_WEAKPOSITIVE,
    e_VXM_POSITIVE,
    e_VXM_STRONGPOSITIVE
  };

  template <typename T1>
  static T1 VirtualXMResult_rect(const T1 f, const T1 f0, const T1 f1,
                                 const T1 f2, const VirtualXMResult v) {
    switch (v) {
    case VirtualXMResult::e_VXM_NEGATIVE: {
      return f;
    }
    case VirtualXMResult::e_VXM_WEAKPOSITIVE: {
      return f0;
    }
    case VirtualXMResult::e_VXM_POSITIVE: {
      return f1;
    }
    case VirtualXMResult::e_VXM_STRONGPOSITIVE: {
      return f2;
    }
    default:
      std::unreachable();
    }
  }

  template <typename T1>
  static T1 VirtualXMResult_rec(const T1 f, const T1 f0, const T1 f1,
                                const T1 f2, const VirtualXMResult v) {
    switch (v) {
    case VirtualXMResult::e_VXM_NEGATIVE: {
      return f;
    }
    case VirtualXMResult::e_VXM_WEAKPOSITIVE: {
      return f0;
    }
    case VirtualXMResult::e_VXM_POSITIVE: {
      return f1;
    }
    case VirtualXMResult::e_VXM_STRONGPOSITIVE: {
      return f2;
    }
    default:
      std::unreachable();
    }
  }

  __attribute__((pure)) static VirtualXMResult
  virtual_crossmatch_safe(const ValidatedMFIConfig &vcfg,
                          const VirtualXMProfile &recipient,
                          const HLATyping &donor);
  enum class TransplantAcceptability {
    e_ACCEPTABLE,
    e_ACCEPTABLE_WITH_DESENSITIZATION,
    e_UNACCEPTABLE_HIGH_RISK,
    e_ABSOLUTE_CONTRAINDICATION
  };

  template <typename T1>
  static T1 TransplantAcceptability_rect(const T1 f, const T1 f0, const T1 f1,
                                         const T1 f2,
                                         const TransplantAcceptability t) {
    switch (t) {
    case TransplantAcceptability::e_ACCEPTABLE: {
      return f;
    }
    case TransplantAcceptability::e_ACCEPTABLE_WITH_DESENSITIZATION: {
      return f0;
    }
    case TransplantAcceptability::e_UNACCEPTABLE_HIGH_RISK: {
      return f1;
    }
    case TransplantAcceptability::e_ABSOLUTE_CONTRAINDICATION: {
      return f2;
    }
    default:
      std::unreachable();
    }
  }

  template <typename T1>
  static T1 TransplantAcceptability_rec(const T1 f, const T1 f0, const T1 f1,
                                        const T1 f2,
                                        const TransplantAcceptability t) {
    switch (t) {
    case TransplantAcceptability::e_ACCEPTABLE: {
      return f;
    }
    case TransplantAcceptability::e_ACCEPTABLE_WITH_DESENSITIZATION: {
      return f0;
    }
    case TransplantAcceptability::e_UNACCEPTABLE_HIGH_RISK: {
      return f1;
    }
    case TransplantAcceptability::e_ABSOLUTE_CONTRAINDICATION: {
      return f2;
    }
    default:
      std::unreachable();
    }
  }

  __attribute__((pure)) static TransplantAcceptability
  transplant_acceptability(const VirtualXMResult vxm,
                           const bool &complement_fixing_dsa);
  __attribute__((pure)) static TransplantAcceptability
  full_virtual_crossmatch_safe(const ValidatedMFIConfig &vcfg,
                               const VirtualXMProfile &recipient,
                               const HLATyping &donor);
  enum class TestConfidence {
    e_CONFIDENCE_HIGH,
    e_CONFIDENCE_MEDIUM,
    e_CONFIDENCE_LOW
  };

  template <typename T1>
  static T1 TestConfidence_rect(const T1 f, const T1 f0, const T1 f1,
                                const TestConfidence t) {
    switch (t) {
    case TestConfidence::e_CONFIDENCE_HIGH: {
      return f;
    }
    case TestConfidence::e_CONFIDENCE_MEDIUM: {
      return f0;
    }
    case TestConfidence::e_CONFIDENCE_LOW: {
      return f1;
    }
    default:
      std::unreachable();
    }
  }

  template <typename T1>
  static T1 TestConfidence_rec(const T1 f, const T1 f0, const T1 f1,
                               const TestConfidence t) {
    switch (t) {
    case TestConfidence::e_CONFIDENCE_HIGH: {
      return f;
    }
    case TestConfidence::e_CONFIDENCE_MEDIUM: {
      return f0;
    }
    case TestConfidence::e_CONFIDENCE_LOW: {
      return f1;
    }
    default:
      std::unreachable();
    }
  }
  enum class CrossmatchResult {
    e_XM_COMPATIBLE,
    e_XM_INCOMPATIBLE,
    e_XM_INCONCLUSIVE,
    e_XM_NOT_DONE
  };

  template <typename T1>
  static T1 CrossmatchResult_rect(const T1 f, const T1 f0, const T1 f1,
                                  const T1 f2, const CrossmatchResult c) {
    switch (c) {
    case CrossmatchResult::e_XM_COMPATIBLE: {
      return f;
    }
    case CrossmatchResult::e_XM_INCOMPATIBLE: {
      return f0;
    }
    case CrossmatchResult::e_XM_INCONCLUSIVE: {
      return f1;
    }
    case CrossmatchResult::e_XM_NOT_DONE: {
      return f2;
    }
    default:
      std::unreachable();
    }
  }

  template <typename T1>
  static T1 CrossmatchResult_rec(const T1 f, const T1 f0, const T1 f1,
                                 const T1 f2, const CrossmatchResult c) {
    switch (c) {
    case CrossmatchResult::e_XM_COMPATIBLE: {
      return f;
    }
    case CrossmatchResult::e_XM_INCOMPATIBLE: {
      return f0;
    }
    case CrossmatchResult::e_XM_INCONCLUSIVE: {
      return f1;
    }
    case CrossmatchResult::e_XM_NOT_DONE: {
      return f2;
    }
    default:
      std::unreachable();
    }
  }

  struct CrossmatchWithUncertainty {
    CrossmatchResult xmu_result;
    unsigned int xmu_method;
    TestConfidence xmu_confidence;

    // ACCESSORS
    __attribute__((pure)) CrossmatchWithUncertainty clone() const {
      return CrossmatchWithUncertainty{
          (*(this)).xmu_result, (*(this)).xmu_method, (*(this)).xmu_confidence};
    }
  };

  __attribute__((pure)) static bool
  safe_to_release(const CrossmatchWithUncertainty &xm);

  struct SafeTransfusionOrder {
    unsigned int sto_recipient_id;
    unsigned int sto_product_id;
    bool sto_compatibility_check;
    CrossmatchWithUncertainty sto_crossmatch;
    unsigned int sto_sample_collection_time;
    unsigned int sto_authorized_by;
    bool sto_emergency_release;

    // ACCESSORS
    __attribute__((pure)) SafeTransfusionOrder clone() const {
      return SafeTransfusionOrder{(*(this)).sto_recipient_id,
                                  (*(this)).sto_product_id,
                                  (*(this)).sto_compatibility_check,
                                  (*(this)).sto_crossmatch.clone(),
                                  (*(this)).sto_sample_collection_time,
                                  (*(this)).sto_authorized_by,
                                  (*(this)).sto_emergency_release};
    }
  };

  __attribute__((pure)) static bool
  order_sample_valid(const unsigned int &collection_time,
                     const unsigned int &current_time);
  __attribute__((pure)) static bool
  transfusion_order_authorized(const SafeTransfusionOrder &order,
                               const unsigned int &current_time);
  __attribute__((pure)) static std::optional<SafeTransfusionOrder>
  create_safe_transfusion_order(unsigned int recipient_id,
                                unsigned int product_id, bool compat_result,
                                CrossmatchWithUncertainty xm,
                                unsigned int sample_time,
                                const unsigned int &current_time,
                                unsigned int authorizer, bool is_emergency);
  static inline const HLATyping donor_hla = HLATyping{List<HLAAllele>::cons(
      HLAAllele{HLALocus::e_LOCUS_A, 2u},
      List<HLAAllele>::cons(
          HLAAllele{HLALocus::e_LOCUS_A, 3u},
          List<HLAAllele>::cons(
              HLAAllele{HLALocus::e_LOCUS_B, 7u},
              List<HLAAllele>::cons(HLAAllele{HLALocus::e_LOCUS_DR, 4u},
                                    List<HLAAllele>::nil()))))};
  static inline const VirtualXMProfile weak_profile = VirtualXMProfile{
      List<EpitopeAntibody>::cons(
          EpitopeAntibody{eplet_65QIA, 2500u, false},
          List<EpitopeAntibody>::cons(EpitopeAntibody{eplet_77N, 800u, false},
                                      List<EpitopeAntibody>::nil())),
      32u, 40u, 2u};
  static inline const VirtualXMProfile strong_profile = VirtualXMProfile{
      List<EpitopeAntibody>::cons(
          EpitopeAntibody{eplet_65QIA, 9000u, true},
          List<EpitopeAntibody>::cons(EpitopeAntibody{eplet_142T, 6000u, false},
                                      List<EpitopeAntibody>::nil())),
      95u, 98u, 5u};
  static inline const CrossmatchWithUncertainty good_crossmatch =
      CrossmatchWithUncertainty{CrossmatchResult::e_XM_COMPATIBLE, 1u,
                                TestConfidence::e_CONFIDENCE_HIGH};
  static inline const CrossmatchWithUncertainty bad_crossmatch =
      CrossmatchWithUncertainty{CrossmatchResult::e_XM_INCOMPATIBLE, 1u,
                                TestConfidence::e_CONFIDENCE_HIGH};
  __attribute__((pure)) static bool
  risk_acceptable(const TransplantAcceptability a);
  static inline const bool sample_virtual_zero_negative = []() {
    switch (classify_mfi_safe(validated_luminex, 0u)) {
    case MFIStrength::e_MFI_NEGATIVE: {
      return true;
    }
    default: {
      return false;
    }
    }
  }();
  static inline const unsigned int sample_dedup_count =
      epitope_dedup(typing_epitopes(donor_hla)).length();
  static inline const bool sample_weak_acceptability = []() {
    switch (full_virtual_crossmatch_safe(validated_luminex, weak_profile,
                                         donor_hla)) {
    case TransplantAcceptability::e_ACCEPTABLE_WITH_DESENSITIZATION: {
      return true;
    }
    default: {
      return false;
    }
    }
  }();
  static inline const bool sample_strong_absolute_contra = []() {
    switch (full_virtual_crossmatch_safe(validated_luminex, strong_profile,
                                         donor_hla)) {
    case TransplantAcceptability::e_ABSOLUTE_CONTRAINDICATION: {
      return true;
    }
    default: {
      return false;
    }
    }
  }();
  static inline const bool sample_strong_has_complement_fixing_dsa =
      has_complement_fixing_dsa(strong_profile, donor_hla);
  static inline const unsigned int sample_strong_max_mfi =
      max_dsa_mfi(strong_profile, donor_hla);
  static inline const unsigned int sample_lab_id =
      validated_luminex.vmc_config.mfi_cfg_lab_id;
  static inline const bool sample_order_created = []() -> bool {
    auto _cs = create_safe_transfusion_order(
        100u, 200u,
        risk_acceptable(full_virtual_crossmatch_safe(validated_luminex,
                                                     weak_profile, donor_hla)),
        good_crossmatch, 0u, 1000u, 77u, false);
    if (_cs.has_value()) {
      const SafeTransfusionOrder &_x = *_cs;
      return true;
    } else {
      return false;
    }
  }();
  static inline const bool sample_order_blocked = []() -> bool {
    auto _cs = create_safe_transfusion_order(
        100u, 201u,
        risk_acceptable(full_virtual_crossmatch_safe(
            validated_luminex, strong_profile, donor_hla)),
        bad_crossmatch, 0u, 1000u, 77u, false);
    if (_cs.has_value()) {
      const SafeTransfusionOrder &_x = *_cs;
      return false;
    } else {
      return true;
    }
  }();
  static inline const bool sample_authorized_order_stays_authorized =
      []() -> bool {
    auto _cs = create_safe_transfusion_order(100u, 202u, true, good_crossmatch,
                                             100u, 200u, 88u, false);
    if (_cs.has_value()) {
      const SafeTransfusionOrder &order = *_cs;
      return transfusion_order_authorized(order, 200u);
    } else {
      return false;
    }
  }();
};

#endif // INCLUDED_VALIDATED_VIRTUAL_CROSSMATCH_TRACE
