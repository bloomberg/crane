#ifndef INCLUDED_HOF_TREE_LOOPIFY
#define INCLUDED_HOF_TREE_LOOPIFY

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
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

struct Uint1 {
  // TYPES
  struct UIntDecimal {
    std::shared_ptr<Uint> d_a0;
  };

  struct UIntHexadecimal {
    std::shared_ptr<Uint0> d_a0;
  };

  using variant_t = std::variant<UIntDecimal, UIntHexadecimal>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  explicit Uint1(UIntDecimal _v) : d_v_(std::move(_v)) {}

  explicit Uint1(UIntHexadecimal _v) : d_v_(std::move(_v)) {}

  static std::shared_ptr<Uint1> uintdecimal(const std::shared_ptr<Uint> &a0) {
    return std::make_shared<Uint1>(UIntDecimal{a0});
  }

  static std::shared_ptr<Uint1> uintdecimal(std::shared_ptr<Uint> &&a0) {
    return std::make_shared<Uint1>(UIntDecimal{std::move(a0)});
  }

  static std::shared_ptr<Uint1>
  uinthexadecimal(const std::shared_ptr<Uint0> &a0) {
    return std::make_shared<Uint1>(UIntHexadecimal{a0});
  }

  static std::shared_ptr<Uint1> uinthexadecimal(std::shared_ptr<Uint0> &&a0) {
    return std::make_shared<Uint1>(UIntHexadecimal{std::move(a0)});
  }

  static std::unique_ptr<Uint1>
  uintdecimal_uptr(const std::shared_ptr<Uint> &a0) {
    return std::make_unique<Uint1>(UIntDecimal{a0});
  }

  static std::unique_ptr<Uint1> uintdecimal_uptr(std::shared_ptr<Uint> &&a0) {
    return std::make_unique<Uint1>(UIntDecimal{std::move(a0)});
  }

  static std::unique_ptr<Uint1>
  uinthexadecimal_uptr(const std::shared_ptr<Uint0> &a0) {
    return std::make_unique<Uint1>(UIntHexadecimal{a0});
  }

  static std::unique_ptr<Uint1>
  uinthexadecimal_uptr(std::shared_ptr<Uint0> &&a0) {
    return std::make_unique<Uint1>(UIntHexadecimal{std::move(a0)});
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

struct HofTreeLoopify {
  template <typename t_A> struct tree {
    // TYPES
    struct Leaf {};

    struct Node {
      std::shared_ptr<tree<t_A>> d_a0;
      t_A d_a1;
      std::shared_ptr<tree<t_A>> d_a2;
    };

    using variant_t = std::variant<Leaf, Node>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    explicit tree(Leaf _v) : d_v_(std::move(_v)) {}

    explicit tree(Node _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<tree<t_A>> leaf() {
      return std::make_shared<tree<t_A>>(Leaf{});
    }

    static std::shared_ptr<tree<t_A>>
    node(const std::shared_ptr<tree<t_A>> &a0, t_A a1,
         const std::shared_ptr<tree<t_A>> &a2) {
      return std::make_shared<tree<t_A>>(Node{a0, std::move(a1), a2});
    }

    static std::shared_ptr<tree<t_A>> node(std::shared_ptr<tree<t_A>> &&a0,
                                           t_A a1,
                                           std::shared_ptr<tree<t_A>> &&a2) {
      return std::make_shared<tree<t_A>>(
          Node{std::move(a0), std::move(a1), std::move(a2)});
    }

    static std::unique_ptr<tree<t_A>> leaf_uptr() {
      return std::make_unique<tree<t_A>>(Leaf{});
    }

    static std::unique_ptr<tree<t_A>>
    node_uptr(const std::shared_ptr<tree<t_A>> &a0, t_A a1,
              const std::shared_ptr<tree<t_A>> &a2) {
      return std::make_unique<tree<t_A>>(Node{a0, std::move(a1), a2});
    }

    static std::unique_ptr<tree<t_A>>
    node_uptr(std::shared_ptr<tree<t_A>> &&a0, t_A a1,
              std::shared_ptr<tree<t_A>> &&a2) {
      return std::make_unique<tree<t_A>>(
          Node{std::move(a0), std::move(a1), std::move(a2)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, typename T2,
            MapsTo<T2, std::shared_ptr<tree<T1>>, T2, T1,
                   std::shared_ptr<tree<T1>>, T2>
                F1>
  static T2 tree_rect(const T2 f, F1 &&f0, const std::shared_ptr<tree<T1>> &t) {
    return std::visit(
        Overloaded{[&](const typename tree<T1>::Leaf _args) -> T2 { return f; },
                   [&](const typename tree<T1>::Node _args) -> T2 {
                     return f0(_args.d_a0, tree_rect<T1, T2>(f, f0, _args.d_a0),
                               _args.d_a1, _args.d_a2,
                               tree_rect<T1, T2>(f, f0, _args.d_a2));
                   }},
        t->v());
  }

  template <typename T1, typename T2,
            MapsTo<T2, std::shared_ptr<tree<T1>>, T2, T1,
                   std::shared_ptr<tree<T1>>, T2>
                F1>
  static T2 tree_rec(const T2 f, F1 &&f0, const std::shared_ptr<tree<T1>> &t) {
    return std::visit(
        Overloaded{[&](const typename tree<T1>::Leaf _args) -> T2 { return f; },
                   [&](const typename tree<T1>::Node _args) -> T2 {
                     return f0(_args.d_a0, tree_rec<T1, T2>(f, f0, _args.d_a0),
                               _args.d_a1, _args.d_a2,
                               tree_rec<T1, T2>(f, f0, _args.d_a2));
                   }},
        t->v());
  }

  static std::shared_ptr<tree<unsigned int>> depth_tree(const unsigned int n);

  template <typename T1, typename T2, MapsTo<T2, T1> F0>
  static std::shared_ptr<tree<T2>>
  tree_map(F0 &&f, const std::shared_ptr<tree<T1>> &t) {
    return std::visit(
        Overloaded{
            [](const typename tree<T1>::Leaf _args)
                -> std::shared_ptr<tree<T2>> { return tree<T2>::leaf(); },
            [&](const typename tree<T1>::Node _args)
                -> std::shared_ptr<tree<T2>> {
              return tree<T2>::node(tree_map<T1, T2>(f, _args.d_a0),
                                    f(_args.d_a1),
                                    tree_map<T1, T2>(f, _args.d_a2));
            }},
        t->v());
  }

  template <typename T1, typename T2, MapsTo<T2, T2, T1, T2> F1>
  static T2 tree_fold(const T2 base, F1 &&f,
                      const std::shared_ptr<tree<T1>> &t) {
    return std::visit(
        Overloaded{
            [&](const typename tree<T1>::Leaf _args) -> T2 { return base; },
            [&](const typename tree<T1>::Node _args) -> T2 {
              return f(tree_fold<T1, T2>(base, f, _args.d_a0), _args.d_a1,
                       tree_fold<T1, T2>(base, f, _args.d_a2));
            }},
        t->v());
  }

  template <typename T1, typename T2, typename T3, MapsTo<T3, T1, T2> F0>
  static std::shared_ptr<tree<T3>>
  tree_zip_with(F0 &&f, const std::shared_ptr<tree<T1>> &t1,
                const std::shared_ptr<tree<T2>> &t2) {
    return std::visit(
        Overloaded{
            [](const typename tree<T1>::Leaf _args)
                -> std::shared_ptr<tree<T3>> { return tree<T3>::leaf(); },
            [&](const typename tree<T1>::Node _args)
                -> std::shared_ptr<tree<T3>> {
              return std::visit(
                  Overloaded{[](const typename tree<T2>::Leaf _args0)
                                 -> std::shared_ptr<tree<T3>> {
                               return tree<T3>::leaf();
                             },
                             [&](const typename tree<T2>::Node _args0)
                                 -> std::shared_ptr<tree<T3>> {
                               return tree<T3>::node(
                                   tree_zip_with<T1, T2, T3>(f, _args.d_a0,
                                                             _args0.d_a0),
                                   f(_args.d_a1, _args0.d_a1),
                                   tree_zip_with<T1, T2, T3>(f, _args.d_a2,
                                                             _args0.d_a2));
                             }},
                  t2->v());
            }},
        t1->v());
  }

  template <typename T1, typename T2, typename T3,
            MapsTo<std::pair<T3, T2>, T3, T1> F0>
  __attribute__((pure)) static std::pair<T3, std::shared_ptr<tree<T2>>>
  tree_map_accum(F0 &&f, const T3 acc, const std::shared_ptr<tree<T1>> &t) {
    return std::visit(
        Overloaded{[&](const typename tree<T1>::Leaf _args)
                       -> std::pair<T3, std::shared_ptr<tree<T2>>> {
                     return std::make_pair(acc, tree<T2>::leaf());
                   },
                   [&](const typename tree<T1>::Node _args)
                       -> std::pair<T3, std::shared_ptr<tree<T2>>> {
                     T3 acc1 =
                         tree_map_accum<T1, T2, T3>(f, acc, _args.d_a0).first;
                     std::shared_ptr<tree<T2>> l_ =
                         tree_map_accum<T1, T2, T3>(f, acc, _args.d_a0).second;
                     T3 acc2 = f(acc1, _args.d_a1).first;
                     T2 x_ = f(acc1, _args.d_a1).second;
                     T3 acc3 =
                         tree_map_accum<T1, T2, T3>(f, acc2, _args.d_a2).first;
                     std::shared_ptr<tree<T2>> r_ =
                         tree_map_accum<T1, T2, T3>(f, acc2, _args.d_a2).second;
                     return std::make_pair(acc3, tree<T2>::node(l_, x_, r_));
                   }},
        t->v());
  }

  static inline const std::shared_ptr<tree<unsigned int>> small_tree =
      tree<unsigned int>::node(
          tree<unsigned int>::node(
              tree<unsigned int>::node(tree<unsigned int>::leaf(), 1u,
                                       tree<unsigned int>::leaf()),
              2u,
              tree<unsigned int>::node(tree<unsigned int>::leaf(), 3u,
                                       tree<unsigned int>::leaf())),
          4u,
          tree<unsigned int>::node(
              tree<unsigned int>::node(tree<unsigned int>::leaf(), 5u,
                                       tree<unsigned int>::leaf()),
              6u,
              tree<unsigned int>::node(tree<unsigned int>::leaf(), 7u,
                                       tree<unsigned int>::leaf())));
  static inline const std::shared_ptr<tree<unsigned int>> mapped =
      tree_map<unsigned int, unsigned int>(
          [](unsigned int x) { return (x * 2u); }, small_tree);
  static inline const unsigned int folded =
      tree_fold<unsigned int, unsigned int>(
          0u,
          [](unsigned int l, unsigned int x, unsigned int r) {
            return ((l + x) + r);
          },
          small_tree);
  static inline const std::shared_ptr<tree<unsigned int>> zipped =
      tree_zip_with<unsigned int, unsigned int, unsigned int>(
          [](unsigned int _x0, unsigned int _x1) -> unsigned int {
            return (_x0 + _x1);
          },
          small_tree, small_tree);
  static inline const std::pair<unsigned int,
                                std::shared_ptr<tree<unsigned int>>>
      accum = tree_map_accum<unsigned int, unsigned int, unsigned int>(
          [](unsigned int s, unsigned int x) {
            return std::make_pair((s + x), s);
          },
          0u, small_tree);
  static inline const std::shared_ptr<tree<unsigned int>> deep =
      depth_tree(Nat::of_num_uint(Uint1::uintdecimal(
          Uint::d5(Uint::d0(Uint::d0(Uint::d0(Uint::d0(Uint::nil()))))))));
};

#endif // INCLUDED_HOF_TREE_LOOPIFY
