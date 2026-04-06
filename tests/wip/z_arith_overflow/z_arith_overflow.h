#ifndef INCLUDED_Z_ARITH_OVERFLOW
#define INCLUDED_Z_ARITH_OVERFLOW

#include <cstdint>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

struct Uint {
  // TYPES
  struct Nil {};

  struct D0 {
    std::shared_ptr<Uint> d_a0;
  };

  struct D1 {
    std::shared_ptr<Uint> d_a0;
  };

  struct D2 {
    std::shared_ptr<Uint> d_a0;
  };

  struct D3 {
    std::shared_ptr<Uint> d_a0;
  };

  struct D4 {
    std::shared_ptr<Uint> d_a0;
  };

  struct D5 {
    std::shared_ptr<Uint> d_a0;
  };

  struct D6 {
    std::shared_ptr<Uint> d_a0;
  };

  struct D7 {
    std::shared_ptr<Uint> d_a0;
  };

  struct D8 {
    std::shared_ptr<Uint> d_a0;
  };

  struct D9 {
    std::shared_ptr<Uint> d_a0;
  };

  using variant_t = std::variant<Nil, D0, D1, D2, D3, D4, D5, D6, D7, D8, D9>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  explicit Uint(Nil _v) : d_v_(std::move(_v)) {}

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

  static std::shared_ptr<Uint> nil() { return std::make_shared<Uint>(Nil{}); }

  static std::shared_ptr<Uint> d0(const std::shared_ptr<Uint> &a0) {
    return std::make_shared<Uint>(D0{a0});
  }

  static std::shared_ptr<Uint> d0(std::shared_ptr<Uint> &&a0) {
    return std::make_shared<Uint>(D0{std::move(a0)});
  }

  static std::shared_ptr<Uint> d1(const std::shared_ptr<Uint> &a0) {
    return std::make_shared<Uint>(D1{a0});
  }

  static std::shared_ptr<Uint> d1(std::shared_ptr<Uint> &&a0) {
    return std::make_shared<Uint>(D1{std::move(a0)});
  }

  static std::shared_ptr<Uint> d2(const std::shared_ptr<Uint> &a0) {
    return std::make_shared<Uint>(D2{a0});
  }

  static std::shared_ptr<Uint> d2(std::shared_ptr<Uint> &&a0) {
    return std::make_shared<Uint>(D2{std::move(a0)});
  }

  static std::shared_ptr<Uint> d3(const std::shared_ptr<Uint> &a0) {
    return std::make_shared<Uint>(D3{a0});
  }

  static std::shared_ptr<Uint> d3(std::shared_ptr<Uint> &&a0) {
    return std::make_shared<Uint>(D3{std::move(a0)});
  }

  static std::shared_ptr<Uint> d4(const std::shared_ptr<Uint> &a0) {
    return std::make_shared<Uint>(D4{a0});
  }

  static std::shared_ptr<Uint> d4(std::shared_ptr<Uint> &&a0) {
    return std::make_shared<Uint>(D4{std::move(a0)});
  }

  static std::shared_ptr<Uint> d5(const std::shared_ptr<Uint> &a0) {
    return std::make_shared<Uint>(D5{a0});
  }

  static std::shared_ptr<Uint> d5(std::shared_ptr<Uint> &&a0) {
    return std::make_shared<Uint>(D5{std::move(a0)});
  }

  static std::shared_ptr<Uint> d6(const std::shared_ptr<Uint> &a0) {
    return std::make_shared<Uint>(D6{a0});
  }

  static std::shared_ptr<Uint> d6(std::shared_ptr<Uint> &&a0) {
    return std::make_shared<Uint>(D6{std::move(a0)});
  }

  static std::shared_ptr<Uint> d7(const std::shared_ptr<Uint> &a0) {
    return std::make_shared<Uint>(D7{a0});
  }

  static std::shared_ptr<Uint> d7(std::shared_ptr<Uint> &&a0) {
    return std::make_shared<Uint>(D7{std::move(a0)});
  }

  static std::shared_ptr<Uint> d8(const std::shared_ptr<Uint> &a0) {
    return std::make_shared<Uint>(D8{a0});
  }

  static std::shared_ptr<Uint> d8(std::shared_ptr<Uint> &&a0) {
    return std::make_shared<Uint>(D8{std::move(a0)});
  }

  static std::shared_ptr<Uint> d9(const std::shared_ptr<Uint> &a0) {
    return std::make_shared<Uint>(D9{a0});
  }

  static std::shared_ptr<Uint> d9(std::shared_ptr<Uint> &&a0) {
    return std::make_shared<Uint>(D9{std::move(a0)});
  }

  static std::unique_ptr<Uint> nil_uptr() {
    return std::make_unique<Uint>(Nil{});
  }

  static std::unique_ptr<Uint> d0_uptr(const std::shared_ptr<Uint> &a0) {
    return std::make_unique<Uint>(D0{a0});
  }

  static std::unique_ptr<Uint> d0_uptr(std::shared_ptr<Uint> &&a0) {
    return std::make_unique<Uint>(D0{std::move(a0)});
  }

  static std::unique_ptr<Uint> d1_uptr(const std::shared_ptr<Uint> &a0) {
    return std::make_unique<Uint>(D1{a0});
  }

  static std::unique_ptr<Uint> d1_uptr(std::shared_ptr<Uint> &&a0) {
    return std::make_unique<Uint>(D1{std::move(a0)});
  }

  static std::unique_ptr<Uint> d2_uptr(const std::shared_ptr<Uint> &a0) {
    return std::make_unique<Uint>(D2{a0});
  }

  static std::unique_ptr<Uint> d2_uptr(std::shared_ptr<Uint> &&a0) {
    return std::make_unique<Uint>(D2{std::move(a0)});
  }

  static std::unique_ptr<Uint> d3_uptr(const std::shared_ptr<Uint> &a0) {
    return std::make_unique<Uint>(D3{a0});
  }

  static std::unique_ptr<Uint> d3_uptr(std::shared_ptr<Uint> &&a0) {
    return std::make_unique<Uint>(D3{std::move(a0)});
  }

  static std::unique_ptr<Uint> d4_uptr(const std::shared_ptr<Uint> &a0) {
    return std::make_unique<Uint>(D4{a0});
  }

  static std::unique_ptr<Uint> d4_uptr(std::shared_ptr<Uint> &&a0) {
    return std::make_unique<Uint>(D4{std::move(a0)});
  }

  static std::unique_ptr<Uint> d5_uptr(const std::shared_ptr<Uint> &a0) {
    return std::make_unique<Uint>(D5{a0});
  }

  static std::unique_ptr<Uint> d5_uptr(std::shared_ptr<Uint> &&a0) {
    return std::make_unique<Uint>(D5{std::move(a0)});
  }

  static std::unique_ptr<Uint> d6_uptr(const std::shared_ptr<Uint> &a0) {
    return std::make_unique<Uint>(D6{a0});
  }

  static std::unique_ptr<Uint> d6_uptr(std::shared_ptr<Uint> &&a0) {
    return std::make_unique<Uint>(D6{std::move(a0)});
  }

  static std::unique_ptr<Uint> d7_uptr(const std::shared_ptr<Uint> &a0) {
    return std::make_unique<Uint>(D7{a0});
  }

  static std::unique_ptr<Uint> d7_uptr(std::shared_ptr<Uint> &&a0) {
    return std::make_unique<Uint>(D7{std::move(a0)});
  }

  static std::unique_ptr<Uint> d8_uptr(const std::shared_ptr<Uint> &a0) {
    return std::make_unique<Uint>(D8{a0});
  }

  static std::unique_ptr<Uint> d8_uptr(std::shared_ptr<Uint> &&a0) {
    return std::make_unique<Uint>(D8{std::move(a0)});
  }

  static std::unique_ptr<Uint> d9_uptr(const std::shared_ptr<Uint> &a0) {
    return std::make_unique<Uint>(D9{a0});
  }

  static std::unique_ptr<Uint> d9_uptr(std::shared_ptr<Uint> &&a0) {
    return std::make_unique<Uint>(D9{std::move(a0)});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
};

struct Uint0 {
  // TYPES
  struct Nil0 {};

  struct D10 {
    std::shared_ptr<Uint0> d_a0;
  };

  struct D11 {
    std::shared_ptr<Uint0> d_a0;
  };

  struct D12 {
    std::shared_ptr<Uint0> d_a0;
  };

  struct D13 {
    std::shared_ptr<Uint0> d_a0;
  };

  struct D14 {
    std::shared_ptr<Uint0> d_a0;
  };

  struct D15 {
    std::shared_ptr<Uint0> d_a0;
  };

  struct D16 {
    std::shared_ptr<Uint0> d_a0;
  };

  struct D17 {
    std::shared_ptr<Uint0> d_a0;
  };

  struct D18 {
    std::shared_ptr<Uint0> d_a0;
  };

  struct D19 {
    std::shared_ptr<Uint0> d_a0;
  };

  struct Da {
    std::shared_ptr<Uint0> d_a0;
  };

  struct Db {
    std::shared_ptr<Uint0> d_a0;
  };

  struct Dc {
    std::shared_ptr<Uint0> d_a0;
  };

  struct Dd {
    std::shared_ptr<Uint0> d_a0;
  };

  struct De {
    std::shared_ptr<Uint0> d_a0;
  };

  struct Df {
    std::shared_ptr<Uint0> d_a0;
  };

  using variant_t = std::variant<Nil0, D10, D11, D12, D13, D14, D15, D16, D17,
                                 D18, D19, Da, Db, Dc, Dd, De, Df>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  explicit Uint0(Nil0 _v) : d_v_(std::move(_v)) {}

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

  static std::shared_ptr<Uint0> nil0() {
    return std::make_shared<Uint0>(Nil0{});
  }

  static std::shared_ptr<Uint0> d10(const std::shared_ptr<Uint0> &a0) {
    return std::make_shared<Uint0>(D10{a0});
  }

  static std::shared_ptr<Uint0> d10(std::shared_ptr<Uint0> &&a0) {
    return std::make_shared<Uint0>(D10{std::move(a0)});
  }

  static std::shared_ptr<Uint0> d11(const std::shared_ptr<Uint0> &a0) {
    return std::make_shared<Uint0>(D11{a0});
  }

  static std::shared_ptr<Uint0> d11(std::shared_ptr<Uint0> &&a0) {
    return std::make_shared<Uint0>(D11{std::move(a0)});
  }

  static std::shared_ptr<Uint0> d12(const std::shared_ptr<Uint0> &a0) {
    return std::make_shared<Uint0>(D12{a0});
  }

  static std::shared_ptr<Uint0> d12(std::shared_ptr<Uint0> &&a0) {
    return std::make_shared<Uint0>(D12{std::move(a0)});
  }

  static std::shared_ptr<Uint0> d13(const std::shared_ptr<Uint0> &a0) {
    return std::make_shared<Uint0>(D13{a0});
  }

  static std::shared_ptr<Uint0> d13(std::shared_ptr<Uint0> &&a0) {
    return std::make_shared<Uint0>(D13{std::move(a0)});
  }

  static std::shared_ptr<Uint0> d14(const std::shared_ptr<Uint0> &a0) {
    return std::make_shared<Uint0>(D14{a0});
  }

  static std::shared_ptr<Uint0> d14(std::shared_ptr<Uint0> &&a0) {
    return std::make_shared<Uint0>(D14{std::move(a0)});
  }

  static std::shared_ptr<Uint0> d15(const std::shared_ptr<Uint0> &a0) {
    return std::make_shared<Uint0>(D15{a0});
  }

  static std::shared_ptr<Uint0> d15(std::shared_ptr<Uint0> &&a0) {
    return std::make_shared<Uint0>(D15{std::move(a0)});
  }

  static std::shared_ptr<Uint0> d16(const std::shared_ptr<Uint0> &a0) {
    return std::make_shared<Uint0>(D16{a0});
  }

  static std::shared_ptr<Uint0> d16(std::shared_ptr<Uint0> &&a0) {
    return std::make_shared<Uint0>(D16{std::move(a0)});
  }

  static std::shared_ptr<Uint0> d17(const std::shared_ptr<Uint0> &a0) {
    return std::make_shared<Uint0>(D17{a0});
  }

  static std::shared_ptr<Uint0> d17(std::shared_ptr<Uint0> &&a0) {
    return std::make_shared<Uint0>(D17{std::move(a0)});
  }

  static std::shared_ptr<Uint0> d18(const std::shared_ptr<Uint0> &a0) {
    return std::make_shared<Uint0>(D18{a0});
  }

  static std::shared_ptr<Uint0> d18(std::shared_ptr<Uint0> &&a0) {
    return std::make_shared<Uint0>(D18{std::move(a0)});
  }

  static std::shared_ptr<Uint0> d19(const std::shared_ptr<Uint0> &a0) {
    return std::make_shared<Uint0>(D19{a0});
  }

  static std::shared_ptr<Uint0> d19(std::shared_ptr<Uint0> &&a0) {
    return std::make_shared<Uint0>(D19{std::move(a0)});
  }

  static std::shared_ptr<Uint0> da(const std::shared_ptr<Uint0> &a0) {
    return std::make_shared<Uint0>(Da{a0});
  }

  static std::shared_ptr<Uint0> da(std::shared_ptr<Uint0> &&a0) {
    return std::make_shared<Uint0>(Da{std::move(a0)});
  }

  static std::shared_ptr<Uint0> db(const std::shared_ptr<Uint0> &a0) {
    return std::make_shared<Uint0>(Db{a0});
  }

  static std::shared_ptr<Uint0> db(std::shared_ptr<Uint0> &&a0) {
    return std::make_shared<Uint0>(Db{std::move(a0)});
  }

  static std::shared_ptr<Uint0> dc(const std::shared_ptr<Uint0> &a0) {
    return std::make_shared<Uint0>(Dc{a0});
  }

  static std::shared_ptr<Uint0> dc(std::shared_ptr<Uint0> &&a0) {
    return std::make_shared<Uint0>(Dc{std::move(a0)});
  }

  static std::shared_ptr<Uint0> dd(const std::shared_ptr<Uint0> &a0) {
    return std::make_shared<Uint0>(Dd{a0});
  }

  static std::shared_ptr<Uint0> dd(std::shared_ptr<Uint0> &&a0) {
    return std::make_shared<Uint0>(Dd{std::move(a0)});
  }

  static std::shared_ptr<Uint0> de(const std::shared_ptr<Uint0> &a0) {
    return std::make_shared<Uint0>(De{a0});
  }

  static std::shared_ptr<Uint0> de(std::shared_ptr<Uint0> &&a0) {
    return std::make_shared<Uint0>(De{std::move(a0)});
  }

  static std::shared_ptr<Uint0> df(const std::shared_ptr<Uint0> &a0) {
    return std::make_shared<Uint0>(Df{a0});
  }

  static std::shared_ptr<Uint0> df(std::shared_ptr<Uint0> &&a0) {
    return std::make_shared<Uint0>(Df{std::move(a0)});
  }

  static std::unique_ptr<Uint0> nil0_uptr() {
    return std::make_unique<Uint0>(Nil0{});
  }

  static std::unique_ptr<Uint0> d10_uptr(const std::shared_ptr<Uint0> &a0) {
    return std::make_unique<Uint0>(D10{a0});
  }

  static std::unique_ptr<Uint0> d10_uptr(std::shared_ptr<Uint0> &&a0) {
    return std::make_unique<Uint0>(D10{std::move(a0)});
  }

  static std::unique_ptr<Uint0> d11_uptr(const std::shared_ptr<Uint0> &a0) {
    return std::make_unique<Uint0>(D11{a0});
  }

  static std::unique_ptr<Uint0> d11_uptr(std::shared_ptr<Uint0> &&a0) {
    return std::make_unique<Uint0>(D11{std::move(a0)});
  }

  static std::unique_ptr<Uint0> d12_uptr(const std::shared_ptr<Uint0> &a0) {
    return std::make_unique<Uint0>(D12{a0});
  }

  static std::unique_ptr<Uint0> d12_uptr(std::shared_ptr<Uint0> &&a0) {
    return std::make_unique<Uint0>(D12{std::move(a0)});
  }

  static std::unique_ptr<Uint0> d13_uptr(const std::shared_ptr<Uint0> &a0) {
    return std::make_unique<Uint0>(D13{a0});
  }

  static std::unique_ptr<Uint0> d13_uptr(std::shared_ptr<Uint0> &&a0) {
    return std::make_unique<Uint0>(D13{std::move(a0)});
  }

  static std::unique_ptr<Uint0> d14_uptr(const std::shared_ptr<Uint0> &a0) {
    return std::make_unique<Uint0>(D14{a0});
  }

  static std::unique_ptr<Uint0> d14_uptr(std::shared_ptr<Uint0> &&a0) {
    return std::make_unique<Uint0>(D14{std::move(a0)});
  }

  static std::unique_ptr<Uint0> d15_uptr(const std::shared_ptr<Uint0> &a0) {
    return std::make_unique<Uint0>(D15{a0});
  }

  static std::unique_ptr<Uint0> d15_uptr(std::shared_ptr<Uint0> &&a0) {
    return std::make_unique<Uint0>(D15{std::move(a0)});
  }

  static std::unique_ptr<Uint0> d16_uptr(const std::shared_ptr<Uint0> &a0) {
    return std::make_unique<Uint0>(D16{a0});
  }

  static std::unique_ptr<Uint0> d16_uptr(std::shared_ptr<Uint0> &&a0) {
    return std::make_unique<Uint0>(D16{std::move(a0)});
  }

  static std::unique_ptr<Uint0> d17_uptr(const std::shared_ptr<Uint0> &a0) {
    return std::make_unique<Uint0>(D17{a0});
  }

  static std::unique_ptr<Uint0> d17_uptr(std::shared_ptr<Uint0> &&a0) {
    return std::make_unique<Uint0>(D17{std::move(a0)});
  }

  static std::unique_ptr<Uint0> d18_uptr(const std::shared_ptr<Uint0> &a0) {
    return std::make_unique<Uint0>(D18{a0});
  }

  static std::unique_ptr<Uint0> d18_uptr(std::shared_ptr<Uint0> &&a0) {
    return std::make_unique<Uint0>(D18{std::move(a0)});
  }

  static std::unique_ptr<Uint0> d19_uptr(const std::shared_ptr<Uint0> &a0) {
    return std::make_unique<Uint0>(D19{a0});
  }

  static std::unique_ptr<Uint0> d19_uptr(std::shared_ptr<Uint0> &&a0) {
    return std::make_unique<Uint0>(D19{std::move(a0)});
  }

  static std::unique_ptr<Uint0> da_uptr(const std::shared_ptr<Uint0> &a0) {
    return std::make_unique<Uint0>(Da{a0});
  }

  static std::unique_ptr<Uint0> da_uptr(std::shared_ptr<Uint0> &&a0) {
    return std::make_unique<Uint0>(Da{std::move(a0)});
  }

  static std::unique_ptr<Uint0> db_uptr(const std::shared_ptr<Uint0> &a0) {
    return std::make_unique<Uint0>(Db{a0});
  }

  static std::unique_ptr<Uint0> db_uptr(std::shared_ptr<Uint0> &&a0) {
    return std::make_unique<Uint0>(Db{std::move(a0)});
  }

  static std::unique_ptr<Uint0> dc_uptr(const std::shared_ptr<Uint0> &a0) {
    return std::make_unique<Uint0>(Dc{a0});
  }

  static std::unique_ptr<Uint0> dc_uptr(std::shared_ptr<Uint0> &&a0) {
    return std::make_unique<Uint0>(Dc{std::move(a0)});
  }

  static std::unique_ptr<Uint0> dd_uptr(const std::shared_ptr<Uint0> &a0) {
    return std::make_unique<Uint0>(Dd{a0});
  }

  static std::unique_ptr<Uint0> dd_uptr(std::shared_ptr<Uint0> &&a0) {
    return std::make_unique<Uint0>(Dd{std::move(a0)});
  }

  static std::unique_ptr<Uint0> de_uptr(const std::shared_ptr<Uint0> &a0) {
    return std::make_unique<Uint0>(De{a0});
  }

  static std::unique_ptr<Uint0> de_uptr(std::shared_ptr<Uint0> &&a0) {
    return std::make_unique<Uint0>(De{std::move(a0)});
  }

  static std::unique_ptr<Uint0> df_uptr(const std::shared_ptr<Uint0> &a0) {
    return std::make_unique<Uint0>(Df{a0});
  }

  static std::unique_ptr<Uint0> df_uptr(std::shared_ptr<Uint0> &&a0) {
    return std::make_unique<Uint0>(Df{std::move(a0)});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
};

struct BinInt {};

struct Uint1 {
  // TYPES
  struct UIntDecimal {
    std::shared_ptr<Uint> d_u;
  };

  struct UIntHexadecimal {
    std::shared_ptr<Uint0> d_u;
  };

  using variant_t = std::variant<UIntDecimal, UIntHexadecimal>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  explicit Uint1(UIntDecimal _v) : d_v_(std::move(_v)) {}

  explicit Uint1(UIntHexadecimal _v) : d_v_(std::move(_v)) {}

  static std::shared_ptr<Uint1> uintdecimal(const std::shared_ptr<Uint> &u) {
    return std::make_shared<Uint1>(UIntDecimal{u});
  }

  static std::shared_ptr<Uint1> uintdecimal(std::shared_ptr<Uint> &&u) {
    return std::make_shared<Uint1>(UIntDecimal{std::move(u)});
  }

  static std::shared_ptr<Uint1>
  uinthexadecimal(const std::shared_ptr<Uint0> &u) {
    return std::make_shared<Uint1>(UIntHexadecimal{u});
  }

  static std::shared_ptr<Uint1> uinthexadecimal(std::shared_ptr<Uint0> &&u) {
    return std::make_shared<Uint1>(UIntHexadecimal{std::move(u)});
  }

  static std::unique_ptr<Uint1>
  uintdecimal_uptr(const std::shared_ptr<Uint> &u) {
    return std::make_unique<Uint1>(UIntDecimal{u});
  }

  static std::unique_ptr<Uint1> uintdecimal_uptr(std::shared_ptr<Uint> &&u) {
    return std::make_unique<Uint1>(UIntDecimal{std::move(u)});
  }

  static std::unique_ptr<Uint1>
  uinthexadecimal_uptr(const std::shared_ptr<Uint0> &u) {
    return std::make_unique<Uint1>(UIntHexadecimal{u});
  }

  static std::unique_ptr<Uint1>
  uinthexadecimal_uptr(std::shared_ptr<Uint0> &&u) {
    return std::make_unique<Uint1>(UIntHexadecimal{std::move(u)});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
};

struct Nat {
  __attribute__((pure)) static unsigned int tail_add(const unsigned int n,
                                                     const unsigned int m);
  __attribute__((pure)) static unsigned int
  tail_addmul(const unsigned int r, const unsigned int n, const unsigned int m);
  __attribute__((pure)) static unsigned int tail_mul(const unsigned int n,
                                                     const unsigned int m);
  __attribute__((pure)) static unsigned int
  of_uint_acc(const std::shared_ptr<Uint> &d, const unsigned int acc);
  __attribute__((pure)) static unsigned int
  of_uint(const std::shared_ptr<Uint> &d);
  __attribute__((pure)) static unsigned int
  of_hex_uint_acc(const std::shared_ptr<Uint0> &d, const unsigned int acc);
  __attribute__((pure)) static unsigned int
  of_hex_uint(const std::shared_ptr<Uint0> &d);
  __attribute__((pure)) static unsigned int
  of_num_uint(const std::shared_ptr<Uint1> &d);
};

struct ZArithOverflow {
  /// Compute 3,100,000,000 via nat -> Z conversion.
  /// 3,100,000,000 fits in unsigned int (< 2^32) and int64_t.
  static inline const int64_t big_z = static_cast<int64_t>(3100000000u);
  /// 3,100,000,000^2 = 9,610,000,000,000,000,000 > INT64_MAX.
  /// In Rocq: perfectly fine (Z is arbitrary precision).
  /// In C++: signed integer multiplication overflow — UB.
  static inline const int64_t overflow_mul = (big_z * big_z);
  /// The result should be positive (product of two positives).
  /// In C++ the overflowed result wraps to a negative value.
  static inline const bool is_positive = INT64_C(0) < overflow_mul;
  /// Addition near INT64_MAX
  static inline const int64_t near_max = static_cast<int64_t>(4000000000u);
  static inline const int64_t near_max_sq = (near_max * near_max);
  /// Negation of the most negative int64_t is also UB
  static inline const int64_t neg_big = (-static_cast<int64_t>(4000000000u));
  static inline const int64_t neg_sq = (neg_big * neg_big);
};

#endif // INCLUDED_Z_ARITH_OVERFLOW
