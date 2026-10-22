#ifndef INCLUDED_NAT_MODULE_FAMILY_RETURNS
#define INCLUDED_NAT_MODULE_FAMILY_RETURNS

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include <algorithm>
#include <atomic>
#include <cstdint>
#include <memory>
#include <optional>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

enum class Reflect;
template <typename A, typename B> struct Sum;
enum class Comparison;
enum class CompareSpecT;
template <typename A> struct Sig;
struct Uint;
struct Signed_int;
struct Uint0;
struct Signed_int0;
struct Decidable;
struct Uint1;
struct Signed_int1;

struct Little {
  static Uint succ(const Uint &d);
};

struct Coq_Little {
  static Uint0 succ(const Uint0 &d);
};

struct Bool {
  static Reflect iff_reflect(bool b);
};
enum class Reflect { REFLECTT, REFLECTF };

template <typename A, typename B> struct Sum {
  // TYPES
  struct Inl {
    A a0;
  };

  struct Inr {
    B a0;
  };

  using variant_t = std::variant<Inl, Inr>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Sum() {}

  explicit Sum(Inl _v) : v_(std::move(_v)) {}

  explicit Sum(Inr _v) : v_(std::move(_v)) {}

  template <typename CraneU0, typename CraneU1>
  Sum(const Sum<CraneU0, CraneU1> &_other)
      : v_([&]() -> variant_t {
          if (std::holds_alternative<typename Sum<CraneU0, CraneU1>::Inl>(
                  _other.v())) {
            const auto &[a0] =
                std::get<typename Sum<CraneU0, CraneU1>::Inl>(_other.v());
            return Inl{[&]() -> A {
              if constexpr (crane_convertible<A, const CraneU0 &>) {
                return crane_convert<A>(a0);
              } else {
                throw std::logic_error("unreachable: inactive constructor "
                                       "field at this instantiation");
              }
            }()};
          } else {
            const auto &[a0] =
                std::get<typename Sum<CraneU0, CraneU1>::Inr>(_other.v());
            return Inr{[&]() -> B {
              if constexpr (crane_convertible<B, const CraneU1 &>) {
                return crane_convert<B>(a0);
              } else {
                throw std::logic_error("unreachable: inactive constructor "
                                       "field at this instantiation");
              }
            }()};
          }
        }()) {}

  static Sum<A, B> inl(A a0) { return Sum<A, B>(Inl{std::move(a0)}); }

  static Sum<A, B> inr(B a0) { return Sum<A, B>(Inr{std::move(a0)}); }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};
enum class Comparison { EQ, LT, GT };
enum class CompareSpecT { COMPEQT, COMPLTT, COMPGTT };
template <typename a = void> using CompSpecT = CompareSpecT;

struct Datatypes {
  static bool xorb(bool b1, bool b2);
  static CompareSpecT CompareSpec2Type(Comparison c);
  template <typename T1>
  static CompSpecT<T1> CompSpec2Type(const T1 &_x, const T1 &_x0,
                                     Comparison x0_);
};

template <typename A> struct Sig {
  // DATA
  A x;

  // ACCESSORS
  Sig<A> clone() const { return {x}; }

  template <typename CraneU> operator Sig<CraneU>() const {
    return {[&]() -> CraneU {
      if constexpr (crane_convertible<CraneU, const A &>) {
        return crane_convert<CraneU>(x);
      } else {
        throw std::logic_error(
            "unreachable: inactive constructor field at this instantiation");
      }
    }()};
  }

  // CREATORS
  static Sig<A> exist(A x) { return {std::move(x)}; }
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
    auto _next = [&](variant_t &_v) -> std::shared_ptr<Uint> {
      if (auto *_alt = std::get_if<D0>(&_v)) {
        if (_alt->a0 && _alt->a0.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          return std::move(_alt->a0);
        }
      }
      if (auto *_alt = std::get_if<D1>(&_v)) {
        if (_alt->a0 && _alt->a0.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          return std::move(_alt->a0);
        }
      }
      if (auto *_alt = std::get_if<D2>(&_v)) {
        if (_alt->a0 && _alt->a0.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          return std::move(_alt->a0);
        }
      }
      if (auto *_alt = std::get_if<D3>(&_v)) {
        if (_alt->a0 && _alt->a0.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          return std::move(_alt->a0);
        }
      }
      if (auto *_alt = std::get_if<D4>(&_v)) {
        if (_alt->a0 && _alt->a0.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          return std::move(_alt->a0);
        }
      }
      if (auto *_alt = std::get_if<D5>(&_v)) {
        if (_alt->a0 && _alt->a0.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          return std::move(_alt->a0);
        }
      }
      if (auto *_alt = std::get_if<D6>(&_v)) {
        if (_alt->a0 && _alt->a0.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          return std::move(_alt->a0);
        }
      }
      if (auto *_alt = std::get_if<D7>(&_v)) {
        if (_alt->a0 && _alt->a0.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          return std::move(_alt->a0);
        }
      }
      if (auto *_alt = std::get_if<D8>(&_v)) {
        if (_alt->a0 && _alt->a0.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          return std::move(_alt->a0);
        }
      }
      if (auto *_alt = std::get_if<D9>(&_v)) {
        if (_alt->a0 && _alt->a0.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          return std::move(_alt->a0);
        }
      }
      return nullptr;
    };
    std::shared_ptr<Uint> _cur = _next(v_mut());
    while (_cur) {
      _cur = _next(_cur->v_mut());
    }
  }

  Uint(const Uint &) = default;
  Uint &operator=(const Uint &) = default;
  Uint(Uint &&) = default;
  Uint &operator=(Uint &&) = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  Uint nzhead() const {
    const Uint *_loop_self = this;
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename Uint::D0>(_sv.v())) {
        const auto &[a0] = std::get<typename Uint::D0>(_sv.v());
        _loop_self = crane_raw(a0);
      } else {
        return *_loop_self;
      }
    }
  }

  Uint unorm() const {
    auto &&_sv = this->nzhead();
    if (std::holds_alternative<typename Uint::Nil>(_sv.v())) {
      return Uint::d0(Uint::nil());
    } else if (std::holds_alternative<typename Uint::D0>(_sv.v())) {
      const auto &[a0] = std::get<typename Uint::D0>(_sv.v());
      return Uint::d0(*a0);
    } else if (std::holds_alternative<typename Uint::D1>(_sv.v())) {
      const auto &[a0] = std::get<typename Uint::D1>(_sv.v());
      return Uint::d1(*a0);
    } else if (std::holds_alternative<typename Uint::D2>(_sv.v())) {
      const auto &[a0] = std::get<typename Uint::D2>(_sv.v());
      return Uint::d2(*a0);
    } else if (std::holds_alternative<typename Uint::D3>(_sv.v())) {
      const auto &[a0] = std::get<typename Uint::D3>(_sv.v());
      return Uint::d3(*a0);
    } else if (std::holds_alternative<typename Uint::D4>(_sv.v())) {
      const auto &[a0] = std::get<typename Uint::D4>(_sv.v());
      return Uint::d4(*a0);
    } else if (std::holds_alternative<typename Uint::D5>(_sv.v())) {
      const auto &[a0] = std::get<typename Uint::D5>(_sv.v());
      return Uint::d5(*a0);
    } else if (std::holds_alternative<typename Uint::D6>(_sv.v())) {
      const auto &[a0] = std::get<typename Uint::D6>(_sv.v());
      return Uint::d6(*a0);
    } else if (std::holds_alternative<typename Uint::D7>(_sv.v())) {
      const auto &[a0] = std::get<typename Uint::D7>(_sv.v());
      return Uint::d7(*a0);
    } else if (std::holds_alternative<typename Uint::D8>(_sv.v())) {
      const auto &[a0] = std::get<typename Uint::D8>(_sv.v());
      return Uint::d8(*a0);
    } else {
      const auto &[a0] = std::get<typename Uint::D9>(_sv.v());
      return Uint::d9(*a0);
    }
  }

  Uint revapp(Uint d_) const {
    const Uint *_loop_self = this;
    Uint _loop_d_ = std::move(d_);
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename Uint::Nil>(_sv.v())) {
        return _loop_d_;
      } else if (std::holds_alternative<typename Uint::D0>(_sv.v())) {
        const auto &[a0] = std::get<typename Uint::D0>(_sv.v());
        _loop_self = crane_raw(a0);
        _loop_d_ = Uint::d0(std::move(_loop_d_));
      } else if (std::holds_alternative<typename Uint::D1>(_sv.v())) {
        const auto &[a0] = std::get<typename Uint::D1>(_sv.v());
        _loop_self = crane_raw(a0);
        _loop_d_ = Uint::d1(std::move(_loop_d_));
      } else if (std::holds_alternative<typename Uint::D2>(_sv.v())) {
        const auto &[a0] = std::get<typename Uint::D2>(_sv.v());
        _loop_self = crane_raw(a0);
        _loop_d_ = Uint::d2(std::move(_loop_d_));
      } else if (std::holds_alternative<typename Uint::D3>(_sv.v())) {
        const auto &[a0] = std::get<typename Uint::D3>(_sv.v());
        _loop_self = crane_raw(a0);
        _loop_d_ = Uint::d3(std::move(_loop_d_));
      } else if (std::holds_alternative<typename Uint::D4>(_sv.v())) {
        const auto &[a0] = std::get<typename Uint::D4>(_sv.v());
        _loop_self = crane_raw(a0);
        _loop_d_ = Uint::d4(std::move(_loop_d_));
      } else if (std::holds_alternative<typename Uint::D5>(_sv.v())) {
        const auto &[a0] = std::get<typename Uint::D5>(_sv.v());
        _loop_self = crane_raw(a0);
        _loop_d_ = Uint::d5(std::move(_loop_d_));
      } else if (std::holds_alternative<typename Uint::D6>(_sv.v())) {
        const auto &[a0] = std::get<typename Uint::D6>(_sv.v());
        _loop_self = crane_raw(a0);
        _loop_d_ = Uint::d6(std::move(_loop_d_));
      } else if (std::holds_alternative<typename Uint::D7>(_sv.v())) {
        const auto &[a0] = std::get<typename Uint::D7>(_sv.v());
        _loop_self = crane_raw(a0);
        _loop_d_ = Uint::d7(std::move(_loop_d_));
      } else if (std::holds_alternative<typename Uint::D8>(_sv.v())) {
        const auto &[a0] = std::get<typename Uint::D8>(_sv.v());
        _loop_self = crane_raw(a0);
        _loop_d_ = Uint::d8(std::move(_loop_d_));
      } else {
        const auto &[a0] = std::get<typename Uint::D9>(_sv.v());
        _loop_self = crane_raw(a0);
        _loop_d_ = Uint::d9(std::move(_loop_d_));
      }
    }
  }

  Uint rev() const { return this->revapp(Uint::nil()); }
};

struct Signed_int {
  // TYPES
  struct Pos {
    Uint d;
  };

  struct Neg {
    Uint d;
  };

  using variant_t = std::variant<Pos, Neg>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Signed_int() {}

  explicit Signed_int(Pos _v) : v_(std::move(_v)) {}

  explicit Signed_int(Neg _v) : v_(std::move(_v)) {}

  static Signed_int pos(Uint d) { return Signed_int(Pos{std::move(d)}); }

  static Signed_int neg(Uint d) { return Signed_int(Neg{std::move(d)}); }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  Signed_int norm() const {
    if (std::holds_alternative<typename Signed_int::Pos>(this->v())) {
      const auto &[d1] = std::get<typename Signed_int::Pos>(this->v());
      return Signed_int::pos(d1.unorm());
    } else {
      const auto &[d1] = std::get<typename Signed_int::Neg>(this->v());
      auto &&_sv0 = d1.nzhead();
      if (std::holds_alternative<typename Uint::Nil>(_sv0.v())) {
        return Signed_int::pos(Uint::d0(Uint::nil()));
      } else if (std::holds_alternative<typename Uint::D0>(_sv0.v())) {
        const auto &[a00] = std::get<typename Uint::D0>(_sv0.v());
        return Signed_int::neg(Uint::d0(*a00));
      } else if (std::holds_alternative<typename Uint::D1>(_sv0.v())) {
        const auto &[a00] = std::get<typename Uint::D1>(_sv0.v());
        return Signed_int::neg(Uint::d1(*a00));
      } else if (std::holds_alternative<typename Uint::D2>(_sv0.v())) {
        const auto &[a00] = std::get<typename Uint::D2>(_sv0.v());
        return Signed_int::neg(Uint::d2(*a00));
      } else if (std::holds_alternative<typename Uint::D3>(_sv0.v())) {
        const auto &[a00] = std::get<typename Uint::D3>(_sv0.v());
        return Signed_int::neg(Uint::d3(*a00));
      } else if (std::holds_alternative<typename Uint::D4>(_sv0.v())) {
        const auto &[a00] = std::get<typename Uint::D4>(_sv0.v());
        return Signed_int::neg(Uint::d4(*a00));
      } else if (std::holds_alternative<typename Uint::D5>(_sv0.v())) {
        const auto &[a00] = std::get<typename Uint::D5>(_sv0.v());
        return Signed_int::neg(Uint::d5(*a00));
      } else if (std::holds_alternative<typename Uint::D6>(_sv0.v())) {
        const auto &[a00] = std::get<typename Uint::D6>(_sv0.v());
        return Signed_int::neg(Uint::d6(*a00));
      } else if (std::holds_alternative<typename Uint::D7>(_sv0.v())) {
        const auto &[a00] = std::get<typename Uint::D7>(_sv0.v());
        return Signed_int::neg(Uint::d7(*a00));
      } else if (std::holds_alternative<typename Uint::D8>(_sv0.v())) {
        const auto &[a00] = std::get<typename Uint::D8>(_sv0.v());
        return Signed_int::neg(Uint::d8(*a00));
      } else {
        const auto &[a00] = std::get<typename Uint::D9>(_sv0.v());
        return Signed_int::neg(Uint::d9(*a00));
      }
    }
  }
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
    auto _next = [&](variant_t &_v) -> std::shared_ptr<Uint0> {
      if (auto *_alt = std::get_if<D10>(&_v)) {
        if (_alt->a0 && _alt->a0.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          return std::move(_alt->a0);
        }
      }
      if (auto *_alt = std::get_if<D11>(&_v)) {
        if (_alt->a0 && _alt->a0.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          return std::move(_alt->a0);
        }
      }
      if (auto *_alt = std::get_if<D12>(&_v)) {
        if (_alt->a0 && _alt->a0.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          return std::move(_alt->a0);
        }
      }
      if (auto *_alt = std::get_if<D13>(&_v)) {
        if (_alt->a0 && _alt->a0.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          return std::move(_alt->a0);
        }
      }
      if (auto *_alt = std::get_if<D14>(&_v)) {
        if (_alt->a0 && _alt->a0.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          return std::move(_alt->a0);
        }
      }
      if (auto *_alt = std::get_if<D15>(&_v)) {
        if (_alt->a0 && _alt->a0.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          return std::move(_alt->a0);
        }
      }
      if (auto *_alt = std::get_if<D16>(&_v)) {
        if (_alt->a0 && _alt->a0.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          return std::move(_alt->a0);
        }
      }
      if (auto *_alt = std::get_if<D17>(&_v)) {
        if (_alt->a0 && _alt->a0.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          return std::move(_alt->a0);
        }
      }
      if (auto *_alt = std::get_if<D18>(&_v)) {
        if (_alt->a0 && _alt->a0.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          return std::move(_alt->a0);
        }
      }
      if (auto *_alt = std::get_if<D19>(&_v)) {
        if (_alt->a0 && _alt->a0.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          return std::move(_alt->a0);
        }
      }
      if (auto *_alt = std::get_if<Da>(&_v)) {
        if (_alt->a0 && _alt->a0.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          return std::move(_alt->a0);
        }
      }
      if (auto *_alt = std::get_if<Db>(&_v)) {
        if (_alt->a0 && _alt->a0.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          return std::move(_alt->a0);
        }
      }
      if (auto *_alt = std::get_if<Dc>(&_v)) {
        if (_alt->a0 && _alt->a0.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          return std::move(_alt->a0);
        }
      }
      if (auto *_alt = std::get_if<Dd>(&_v)) {
        if (_alt->a0 && _alt->a0.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          return std::move(_alt->a0);
        }
      }
      if (auto *_alt = std::get_if<De>(&_v)) {
        if (_alt->a0 && _alt->a0.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          return std::move(_alt->a0);
        }
      }
      if (auto *_alt = std::get_if<Df>(&_v)) {
        if (_alt->a0 && _alt->a0.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          return std::move(_alt->a0);
        }
      }
      return nullptr;
    };
    std::shared_ptr<Uint0> _cur = _next(v_mut());
    while (_cur) {
      _cur = _next(_cur->v_mut());
    }
  }

  Uint0(const Uint0 &) = default;
  Uint0 &operator=(const Uint0 &) = default;
  Uint0(Uint0 &&) = default;
  Uint0 &operator=(Uint0 &&) = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  Uint0 nzhead0() const {
    const Uint0 *_loop_self = this;
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename Uint0::D10>(_sv.v())) {
        const auto &[a0] = std::get<typename Uint0::D10>(_sv.v());
        _loop_self = crane_raw(a0);
      } else {
        return *_loop_self;
      }
    }
  }

  Uint0 unorm0() const {
    auto &&_sv = this->nzhead0();
    if (std::holds_alternative<typename Uint0::Nil0>(_sv.v())) {
      return Uint0::d10(Uint0::nil0());
    } else if (std::holds_alternative<typename Uint0::D10>(_sv.v())) {
      const auto &[a0] = std::get<typename Uint0::D10>(_sv.v());
      return Uint0::d10(*a0);
    } else if (std::holds_alternative<typename Uint0::D11>(_sv.v())) {
      const auto &[a0] = std::get<typename Uint0::D11>(_sv.v());
      return Uint0::d11(*a0);
    } else if (std::holds_alternative<typename Uint0::D12>(_sv.v())) {
      const auto &[a0] = std::get<typename Uint0::D12>(_sv.v());
      return Uint0::d12(*a0);
    } else if (std::holds_alternative<typename Uint0::D13>(_sv.v())) {
      const auto &[a0] = std::get<typename Uint0::D13>(_sv.v());
      return Uint0::d13(*a0);
    } else if (std::holds_alternative<typename Uint0::D14>(_sv.v())) {
      const auto &[a0] = std::get<typename Uint0::D14>(_sv.v());
      return Uint0::d14(*a0);
    } else if (std::holds_alternative<typename Uint0::D15>(_sv.v())) {
      const auto &[a0] = std::get<typename Uint0::D15>(_sv.v());
      return Uint0::d15(*a0);
    } else if (std::holds_alternative<typename Uint0::D16>(_sv.v())) {
      const auto &[a0] = std::get<typename Uint0::D16>(_sv.v());
      return Uint0::d16(*a0);
    } else if (std::holds_alternative<typename Uint0::D17>(_sv.v())) {
      const auto &[a0] = std::get<typename Uint0::D17>(_sv.v());
      return Uint0::d17(*a0);
    } else if (std::holds_alternative<typename Uint0::D18>(_sv.v())) {
      const auto &[a0] = std::get<typename Uint0::D18>(_sv.v());
      return Uint0::d18(*a0);
    } else if (std::holds_alternative<typename Uint0::D19>(_sv.v())) {
      const auto &[a0] = std::get<typename Uint0::D19>(_sv.v());
      return Uint0::d19(*a0);
    } else if (std::holds_alternative<typename Uint0::Da>(_sv.v())) {
      const auto &[a0] = std::get<typename Uint0::Da>(_sv.v());
      return Uint0::da(*a0);
    } else if (std::holds_alternative<typename Uint0::Db>(_sv.v())) {
      const auto &[a0] = std::get<typename Uint0::Db>(_sv.v());
      return Uint0::db(*a0);
    } else if (std::holds_alternative<typename Uint0::Dc>(_sv.v())) {
      const auto &[a0] = std::get<typename Uint0::Dc>(_sv.v());
      return Uint0::dc(*a0);
    } else if (std::holds_alternative<typename Uint0::Dd>(_sv.v())) {
      const auto &[a0] = std::get<typename Uint0::Dd>(_sv.v());
      return Uint0::dd(*a0);
    } else if (std::holds_alternative<typename Uint0::De>(_sv.v())) {
      const auto &[a0] = std::get<typename Uint0::De>(_sv.v());
      return Uint0::de(*a0);
    } else {
      const auto &[a0] = std::get<typename Uint0::Df>(_sv.v());
      return Uint0::df(*a0);
    }
  }

  Uint0 revapp0(Uint0 d_) const {
    const Uint0 *_loop_self = this;
    Uint0 _loop_d_ = std::move(d_);
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename Uint0::Nil0>(_sv.v())) {
        return _loop_d_;
      } else if (std::holds_alternative<typename Uint0::D10>(_sv.v())) {
        const auto &[a0] = std::get<typename Uint0::D10>(_sv.v());
        _loop_self = crane_raw(a0);
        _loop_d_ = Uint0::d10(std::move(_loop_d_));
      } else if (std::holds_alternative<typename Uint0::D11>(_sv.v())) {
        const auto &[a0] = std::get<typename Uint0::D11>(_sv.v());
        _loop_self = crane_raw(a0);
        _loop_d_ = Uint0::d11(std::move(_loop_d_));
      } else if (std::holds_alternative<typename Uint0::D12>(_sv.v())) {
        const auto &[a0] = std::get<typename Uint0::D12>(_sv.v());
        _loop_self = crane_raw(a0);
        _loop_d_ = Uint0::d12(std::move(_loop_d_));
      } else if (std::holds_alternative<typename Uint0::D13>(_sv.v())) {
        const auto &[a0] = std::get<typename Uint0::D13>(_sv.v());
        _loop_self = crane_raw(a0);
        _loop_d_ = Uint0::d13(std::move(_loop_d_));
      } else if (std::holds_alternative<typename Uint0::D14>(_sv.v())) {
        const auto &[a0] = std::get<typename Uint0::D14>(_sv.v());
        _loop_self = crane_raw(a0);
        _loop_d_ = Uint0::d14(std::move(_loop_d_));
      } else if (std::holds_alternative<typename Uint0::D15>(_sv.v())) {
        const auto &[a0] = std::get<typename Uint0::D15>(_sv.v());
        _loop_self = crane_raw(a0);
        _loop_d_ = Uint0::d15(std::move(_loop_d_));
      } else if (std::holds_alternative<typename Uint0::D16>(_sv.v())) {
        const auto &[a0] = std::get<typename Uint0::D16>(_sv.v());
        _loop_self = crane_raw(a0);
        _loop_d_ = Uint0::d16(std::move(_loop_d_));
      } else if (std::holds_alternative<typename Uint0::D17>(_sv.v())) {
        const auto &[a0] = std::get<typename Uint0::D17>(_sv.v());
        _loop_self = crane_raw(a0);
        _loop_d_ = Uint0::d17(std::move(_loop_d_));
      } else if (std::holds_alternative<typename Uint0::D18>(_sv.v())) {
        const auto &[a0] = std::get<typename Uint0::D18>(_sv.v());
        _loop_self = crane_raw(a0);
        _loop_d_ = Uint0::d18(std::move(_loop_d_));
      } else if (std::holds_alternative<typename Uint0::D19>(_sv.v())) {
        const auto &[a0] = std::get<typename Uint0::D19>(_sv.v());
        _loop_self = crane_raw(a0);
        _loop_d_ = Uint0::d19(std::move(_loop_d_));
      } else if (std::holds_alternative<typename Uint0::Da>(_sv.v())) {
        const auto &[a0] = std::get<typename Uint0::Da>(_sv.v());
        _loop_self = crane_raw(a0);
        _loop_d_ = Uint0::da(std::move(_loop_d_));
      } else if (std::holds_alternative<typename Uint0::Db>(_sv.v())) {
        const auto &[a0] = std::get<typename Uint0::Db>(_sv.v());
        _loop_self = crane_raw(a0);
        _loop_d_ = Uint0::db(std::move(_loop_d_));
      } else if (std::holds_alternative<typename Uint0::Dc>(_sv.v())) {
        const auto &[a0] = std::get<typename Uint0::Dc>(_sv.v());
        _loop_self = crane_raw(a0);
        _loop_d_ = Uint0::dc(std::move(_loop_d_));
      } else if (std::holds_alternative<typename Uint0::Dd>(_sv.v())) {
        const auto &[a0] = std::get<typename Uint0::Dd>(_sv.v());
        _loop_self = crane_raw(a0);
        _loop_d_ = Uint0::dd(std::move(_loop_d_));
      } else if (std::holds_alternative<typename Uint0::De>(_sv.v())) {
        const auto &[a0] = std::get<typename Uint0::De>(_sv.v());
        _loop_self = crane_raw(a0);
        _loop_d_ = Uint0::de(std::move(_loop_d_));
      } else {
        const auto &[a0] = std::get<typename Uint0::Df>(_sv.v());
        _loop_self = crane_raw(a0);
        _loop_d_ = Uint0::df(std::move(_loop_d_));
      }
    }
  }

  Uint0 rev0() const { return this->revapp0(Uint0::nil0()); }
};

struct Signed_int0 {
  // TYPES
  struct Pos0 {
    Uint0 d;
  };

  struct Neg0 {
    Uint0 d;
  };

  using variant_t = std::variant<Pos0, Neg0>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Signed_int0() {}

  explicit Signed_int0(Pos0 _v) : v_(std::move(_v)) {}

  explicit Signed_int0(Neg0 _v) : v_(std::move(_v)) {}

  static Signed_int0 pos0(Uint0 d) { return Signed_int0(Pos0{std::move(d)}); }

  static Signed_int0 neg0(Uint0 d) { return Signed_int0(Neg0{std::move(d)}); }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  Signed_int0 norm0() const {
    if (std::holds_alternative<typename Signed_int0::Pos0>(this->v())) {
      const auto &[d1] = std::get<typename Signed_int0::Pos0>(this->v());
      return Signed_int0::pos0(d1.unorm0());
    } else {
      const auto &[d1] = std::get<typename Signed_int0::Neg0>(this->v());
      auto &&_sv0 = d1.nzhead0();
      if (std::holds_alternative<typename Uint0::Nil0>(_sv0.v())) {
        return Signed_int0::pos0(Uint0::d10(Uint0::nil0()));
      } else if (std::holds_alternative<typename Uint0::D10>(_sv0.v())) {
        const auto &[a00] = std::get<typename Uint0::D10>(_sv0.v());
        return Signed_int0::neg0(Uint0::d10(*a00));
      } else if (std::holds_alternative<typename Uint0::D11>(_sv0.v())) {
        const auto &[a00] = std::get<typename Uint0::D11>(_sv0.v());
        return Signed_int0::neg0(Uint0::d11(*a00));
      } else if (std::holds_alternative<typename Uint0::D12>(_sv0.v())) {
        const auto &[a00] = std::get<typename Uint0::D12>(_sv0.v());
        return Signed_int0::neg0(Uint0::d12(*a00));
      } else if (std::holds_alternative<typename Uint0::D13>(_sv0.v())) {
        const auto &[a00] = std::get<typename Uint0::D13>(_sv0.v());
        return Signed_int0::neg0(Uint0::d13(*a00));
      } else if (std::holds_alternative<typename Uint0::D14>(_sv0.v())) {
        const auto &[a00] = std::get<typename Uint0::D14>(_sv0.v());
        return Signed_int0::neg0(Uint0::d14(*a00));
      } else if (std::holds_alternative<typename Uint0::D15>(_sv0.v())) {
        const auto &[a00] = std::get<typename Uint0::D15>(_sv0.v());
        return Signed_int0::neg0(Uint0::d15(*a00));
      } else if (std::holds_alternative<typename Uint0::D16>(_sv0.v())) {
        const auto &[a00] = std::get<typename Uint0::D16>(_sv0.v());
        return Signed_int0::neg0(Uint0::d16(*a00));
      } else if (std::holds_alternative<typename Uint0::D17>(_sv0.v())) {
        const auto &[a00] = std::get<typename Uint0::D17>(_sv0.v());
        return Signed_int0::neg0(Uint0::d17(*a00));
      } else if (std::holds_alternative<typename Uint0::D18>(_sv0.v())) {
        const auto &[a00] = std::get<typename Uint0::D18>(_sv0.v());
        return Signed_int0::neg0(Uint0::d18(*a00));
      } else if (std::holds_alternative<typename Uint0::D19>(_sv0.v())) {
        const auto &[a00] = std::get<typename Uint0::D19>(_sv0.v());
        return Signed_int0::neg0(Uint0::d19(*a00));
      } else if (std::holds_alternative<typename Uint0::Da>(_sv0.v())) {
        const auto &[a00] = std::get<typename Uint0::Da>(_sv0.v());
        return Signed_int0::neg0(Uint0::da(*a00));
      } else if (std::holds_alternative<typename Uint0::Db>(_sv0.v())) {
        const auto &[a00] = std::get<typename Uint0::Db>(_sv0.v());
        return Signed_int0::neg0(Uint0::db(*a00));
      } else if (std::holds_alternative<typename Uint0::Dc>(_sv0.v())) {
        const auto &[a00] = std::get<typename Uint0::Dc>(_sv0.v());
        return Signed_int0::neg0(Uint0::dc(*a00));
      } else if (std::holds_alternative<typename Uint0::Dd>(_sv0.v())) {
        const auto &[a00] = std::get<typename Uint0::Dd>(_sv0.v());
        return Signed_int0::neg0(Uint0::dd(*a00));
      } else if (std::holds_alternative<typename Uint0::De>(_sv0.v())) {
        const auto &[a00] = std::get<typename Uint0::De>(_sv0.v());
        return Signed_int0::neg0(Uint0::de(*a00));
      } else {
        const auto &[a00] = std::get<typename Uint0::Df>(_sv0.v());
        return Signed_int0::neg0(Uint0::df(*a00));
      }
    }
  }
};

struct Decidable {
  bool Decidable_witness;
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

struct Signed_int1 {
  // TYPES
  struct IntDecimal {
    Signed_int i;
  };

  struct IntHexadecimal {
    Signed_int0 i;
  };

  using variant_t = std::variant<IntDecimal, IntHexadecimal>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Signed_int1() {}

  explicit Signed_int1(IntDecimal _v) : v_(std::move(_v)) {}

  explicit Signed_int1(IntHexadecimal _v) : v_(std::move(_v)) {}

  static Signed_int1 intdecimal(Signed_int i) {
    return Signed_int1(IntDecimal{std::move(i)});
  }

  static Signed_int1 inthexadecimal(Signed_int0 i) {
    return Signed_int1(IntHexadecimal{std::move(i)});
  }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

template <typename M>
concept PrivateBitwiseSpec = true;

struct Nat {
  using t = uint64_t;
  static constexpr uint64_t zero = UINT64_C(0);
  static constexpr uint64_t one = UINT64_C(1);
  static constexpr uint64_t two = UINT64_C(2);
  static uint64_t succ(uint64_t x);
  static Comparison compare(uint64_t n, uint64_t m);
  static bool even(uint64_t n);
  static bool odd(uint64_t n);
  static uint64_t pow(uint64_t n, uint64_t m);
  static uint64_t tail_add(uint64_t n, uint64_t m);
  static uint64_t tail_addmul(uint64_t r, uint64_t n, uint64_t m);
  static uint64_t tail_mul(uint64_t n, uint64_t m);
  static uint64_t of_uint_acc(const Uint &d, uint64_t acc);
  static uint64_t of_uint(const Uint &d);
  static uint64_t of_hex_uint_acc(const Uint0 &d, uint64_t acc);
  static uint64_t of_hex_uint(const Uint0 &d);
  static uint64_t of_num_uint(const Uint1 &d);
  static Uint to_little_uint(uint64_t n, Uint acc);
  static Uint to_uint(uint64_t n);
  static Uint0 to_little_hex_uint(uint64_t n, Uint0 acc);
  static Uint0 to_hex_uint(uint64_t n);
  static Uint1 to_num_uint(uint64_t n);
  static Uint1 to_num_hex_uint(uint64_t n);
  static std::optional<uint64_t> of_int(const Signed_int &d);
  static std::optional<uint64_t> of_hex_int(const Signed_int0 &d);
  static std::optional<uint64_t> of_num_int(const Signed_int1 &d);
  static Signed_int to_int(uint64_t n);
  static Signed_int0 to_hex_int(uint64_t n);
  static Signed_int1 to_num_int(uint64_t n);
  static std::pair<uint64_t, uint64_t> divmod(uint64_t x, uint64_t y,
                                              uint64_t q, uint64_t u);
  static uint64_t gcd(uint64_t a, uint64_t b);
  static uint64_t square(uint64_t n);
  static uint64_t sqrt_iter(uint64_t k, uint64_t p, uint64_t q, uint64_t r);
  static uint64_t sqrt(uint64_t n);
  static uint64_t log2_iter(uint64_t k, uint64_t p, uint64_t q, uint64_t r);
  static uint64_t log2(uint64_t n);
  static uint64_t div2(uint64_t n);
  static bool testbit(uint64_t a, uint64_t n);
  static uint64_t shiftl(uint64_t a, uint64_t n);
  static uint64_t shiftr(uint64_t a, uint64_t n);

  template <typename F0>
  static uint64_t bitwise(F0 &&op, uint64_t n, uint64_t a, uint64_t b) {
    if (n <= 0) {
      return UINT64_C(0);
    } else {
      uint64_t n_ = n - 1;
      return ((op(odd(a), odd(b)) ? UINT64_C(1) : UINT64_C(0)) +
              (UINT64_C(2) * bitwise(op, n_, div2(a), div2(b))));
    }
  }

  static uint64_t land(uint64_t a, uint64_t b);
  static uint64_t lor(uint64_t a, uint64_t b);
  static uint64_t ldiff(uint64_t a, uint64_t b);
  static uint64_t lxor(uint64_t a, uint64_t b);

  template <typename T1, typename F1>
  static T1 recursion(T1 x, F1 &&f0, uint64_t n) {
    if (n <= 0) {
      return x;
    } else {
      uint64_t n0 = n - 1;
      return f0(n0, recursion<T1>(std::move(x), f0, n0));
    }
  }

  static Decidable Decidable_eq_nat(uint64_t x, uint64_t y);
  static Decidable Decidable_le_nat(uint64_t x, uint64_t y);
  static bool eq_dec(uint64_t n, uint64_t m);
  static Reflect leb_spec0(uint64_t x, uint64_t y);
  static Reflect ltb_spec0(uint64_t x, uint64_t y);

  struct Private_OrderTac {
    struct IsTotal {};

    struct Tac {};
  };

  template <typename T1, typename T2, typename F2>
    requires std::is_invocable_r_v<T2, const F2 &, T1 &, crane::fn<T2(T1)>>
  static T2
  measure_right_induction(std::type_identity_t<crane::fn<uint64_t(T1)>> f,
                          uint64_t, F2 &&iH, const T1 &x) {
    uint64_t t0 = f(x);
    auto f0_impl = [=, f = std::move(f)](auto &_self_f0, uint64_t, T1 y) -> T2 {
      return iH(y, [=](const T1 &y_) {
        uint64_t y0 = f(y_);
        return _self_f0(_self_f0, y0, y_);
      });
    };
    {
      uint64_t _lc1_x0 = t0;
      T1 _lc1_y = x;
      return f0_impl(f0_impl, _lc1_x0, std::move(_lc1_y));
    }
  }

  template <typename T1, typename T2, typename F0, typename F2>
  static T2 measure_left_induction(F0 &&f, uint64_t _x, F2 &&iH, const T1 &x) {
    return measure_right_induction<T1, T2>(f, _x, iH, x);
  }

  template <typename T1, typename T2, typename F0>
  static T2 measure_induction(
      F0 &&f, std::type_identity_t<crane::fn<T2(T1, crane::fn<T2(T1)>)>> iH,
      const T1 &x) {
    return measure_right_induction<T1, T2>(
        f, UINT64_C(0),
        [=, iH = std::move(iH)](const T1 &y, crane::fn<T2(T1)> iH_) {
          return iH(y, [=](const T1 &y0) { return iH_(y0); });
        },
        x);
  }

  struct Private_Tac {};

  struct Private_Dec {
    template <typename T1, typename F2>
      requires std::is_invocable_r_v<T1, F2 &, uint64_t &, uint64_t, const T1 &>
    static T1 max_case_strong(uint64_t n, uint64_t m, F2 &&compat, const T1 &hl,
                              const T1 &hr) {
      CompareSpecT c =
          Datatypes::template CompSpec2Type<uint64_t>(n, m, compare(n, m));
      switch (c) {
      case CompareSpecT::COMPGTT: {
        return compat(n, std::max(n, m), hl);
      }
      default: {
        return compat(m, std::max(n, m), hr);
      }
      }
    }

    template <typename T1, typename F2>
    static T1 max_case(uint64_t n, uint64_t m, F2 &&x, const T1 &x0,
                       const T1 &x1) {
      return max_case_strong<T1>(
          n, m, x, [=]() { return x0; }(), [=]() { return x1; }());
    }

    static bool max_dec(uint64_t n, uint64_t m);

    template <typename T1, typename F2>
      requires std::is_invocable_r_v<T1, F2 &, uint64_t &, uint64_t, const T1 &>
    static T1 min_case_strong(uint64_t n, uint64_t m, F2 &&compat, const T1 &hl,
                              const T1 &hr) {
      CompareSpecT c =
          Datatypes::template CompSpec2Type<uint64_t>(n, m, compare(n, m));
      switch (c) {
      case CompareSpecT::COMPGTT: {
        return compat(m, std::min(n, m), hr);
      }
      default: {
        return compat(n, std::min(n, m), hl);
      }
      }
    }

    template <typename T1, typename F2>
    static T1 min_case(uint64_t n, uint64_t m, F2 &&x, const T1 &x0,
                       const T1 &x1) {
      return min_case_strong<T1>(
          n, m, x, [=]() { return x0; }(), [=]() { return x1; }());
    }

    static bool min_dec(uint64_t n, uint64_t m);
  };

  template <typename T1>
  static T1 max_case_strong(uint64_t n, uint64_t m, const T1 &x, const T1 &x0) {
    return Private_Dec::template max_case_strong<T1>(
        n, m, [](uint64_t, uint64_t, T1 x1) { return x1; }, x, x0);
  }

  template <typename T1>
  static T1 max_case(uint64_t n, uint64_t m, const T1 &x, const T1 &x0) {
    return max_case_strong<T1>(
        n, m, [=]() { return x; }(), [=]() { return x0; }());
  }

  static bool max_dec(uint64_t x0_, uint64_t x1_);

  template <typename T1>
  static T1 min_case_strong(uint64_t n, uint64_t m, const T1 &x, const T1 &x0) {
    return Private_Dec::template min_case_strong<T1>(
        n, m, [](uint64_t, uint64_t, T1 x1) { return x1; }, x, x0);
  }

  template <typename T1>
  static T1 min_case(uint64_t n, uint64_t m, const T1 &x, const T1 &x0) {
    return min_case_strong<T1>(
        n, m, [=]() { return x; }(), [=]() { return x0; }());
  }

  static bool min_dec(uint64_t x0_, uint64_t x1_);

  struct Private_Parity {};

  template <typename T1, typename T2, typename F0, typename F3>
  static T2 iter_rect(F0 &&f, T1 a, T2 h0, F3 &&hS, uint64_t n) {
    if (n <= 0) {
      return h0;
    } else {
      uint64_t n0 = n - 1;
      return hS(
          n0,
          [&]() {
            auto f0_impl = [&](auto &_self_f0, uint64_t n1) -> T1 {
              if (n1 <= 0) {
                return a;
              } else {
                uint64_t n2 = n1 - 1;
                return f(_self_f0(_self_f0, n2));
              }
            };
            auto f0 = [&](uint64_t n1) -> T1 { return f0_impl(f0_impl, n1); };
            return f0(n0);
          }(),
          iter_rect<T1, T2>(f, a, std::move(h0), hS, n0));
    }
  }

  struct PrivateImplementsBitwiseSpec {
    static inline const crane::obj div2_double = crane::obj();
    static inline const crane::obj div2_succ_double = crane::obj();
    static inline const crane::obj testbit_odd_0 = crane::obj();
    static inline const crane::obj testbit_even_0 = crane::obj();
    static inline const crane::obj shiftl_spec_low = crane::obj();
    static inline const crane::obj div2_bitwise = crane::obj();
    static inline const crane::obj odd_bitwise = crane::obj();
    static inline const crane::obj testbit_bitwise_1 = crane::obj();
    static inline const crane::obj testbit_bitwise_2 = crane::obj();
    static inline const crane::obj land_spec = crane::obj();
    static inline const crane::obj ldiff_spec = crane::obj();
    static inline const crane::obj lor_spec = crane::obj();
    static inline const crane::obj lxor_spec = crane::obj();
    static inline const crane::obj div2_spec = crane::obj();
    static inline const crane::obj testbit_odd_succ = crane::obj();
    static inline const crane::obj testbit_even_succ = crane::obj();
    static inline const crane::obj testbit_neg_r = crane::obj();
    static inline const crane::obj shiftl_spec_high = crane::obj();
    static inline const crane::obj shiftr_spec = crane::obj();
  };

  static_assert(PrivateBitwiseSpec<PrivateImplementsBitwiseSpec>);

  struct Private_NZPow {};

  struct Private_NZSqrt {};

  static uint64_t sqrt_up(uint64_t a);
  static uint64_t log2_up(uint64_t a);

  struct Private_NZGcdProp {};

  struct Private_NDivProp {
    struct Private_NZDiv {};
  };

  struct Div0 {};

  struct Private_NLcmProp {
    static uint64_t lcm(uint64_t a, uint64_t b);
  };

  static uint64_t lcm(uint64_t a, uint64_t b);

  struct Lcm0 {};

  static Reflect eqb_spec(uint64_t x, uint64_t y);
  static uint64_t b2n(bool b);
  static uint64_t setbit(uint64_t a, uint64_t n);
  static uint64_t clearbit(uint64_t a, uint64_t n);
  static uint64_t ones(uint64_t n);
  static uint64_t lnot(uint64_t a, uint64_t n);
  static bool Even_Odd_dec(uint64_t n);
  using EvenT = Sig<uint64_t>;
  using OddT = Sig<uint64_t>;
  static inline const EvenT EvenT_0 = Sig<uint64_t>::exist(UINT64_C(0));
  static EvenT EvenT_2(uint64_t _x, const Sig<uint64_t> &h0);
  static inline const OddT OddT_1 = Sig<uint64_t>::exist(UINT64_C(0));
  static OddT OddT_2(uint64_t _x, const Sig<uint64_t> &h0);
  static OddT EvenT_S_OddT(uint64_t _x, const Sig<uint64_t> &h);
  static EvenT OddT_S_EvenT(uint64_t _x, const Sig<uint64_t> &h);
  static EvenT even_EvenT(uint64_t n);
  static OddT odd_OddT(uint64_t n);
  static EvenT Even_EvenT(uint64_t x0_);
  static OddT Odd_OddT(uint64_t x0_);
  static Sum<EvenT, OddT> EvenT_OddT_dec(uint64_t n);

  template <typename T1, typename T2, typename F0, typename F2>
  static T1
  OddT_EvenT_rect(F0 &&hQP, T2 hQ0, F2 &&hPQ, uint64_t n0,
                  const Sig<uint64_t> &h) { // Precondition: n == (2 * m + 1)
    if (n0 <= 0) {
      const auto &[x0] = h;
      if (x0 <= 0) {
        throw std::logic_error("absurd case");
      } else {
        uint64_t _x = x0 - 1;
        throw std::logic_error("absurd case");
      }
    } else {
      uint64_t n = n0 - 1;
      if (n <= 0) {
        return hQP(UINT64_C(0), EvenT_0, std::move(hQ0));
      } else {
        uint64_t n1 = n - 1;
        EvenT hES = OddT_S_EvenT((n1 + 1), h);
        OddT hO = EvenT_S_OddT(n1, hES);
        return hQP(
            (n1 + 1), std::move(hES),
            hPQ(n1, hO,
                OddT_EvenT_rect<T1, T2>(hQP, std::move(hQ0), hPQ, n1, hO)));
      }
    }
  }

  template <typename T1, typename T2, typename F0, typename F2>
  static T2
  EvenT_OddT_rect(F0 &&hQP, T2 hQ0, F2 &&hPQ, uint64_t n0,
                  const Sig<uint64_t> &hES) { // Precondition: n == (2 * m)
    if (n0 <= 0) {
      return hQ0;
    } else {
      uint64_t n = n0 - 1;
      OddT hO = EvenT_S_OddT(n, hES);
      return hPQ(n, hO,
                 OddT_EvenT_rect<T1, T2>(hQP, std::move(hQ0), hPQ, n, hO));
    }
  }
};

struct NatModuleFamilyReturns {
  using X = Nat;
  static inline const uint64_t result = std::max(UINT64_C(3), UINT64_C(4));
};

template <typename T1>
CompSpecT<T1> Datatypes::CompSpec2Type(const T1 &, const T1 &, Comparison x0_) {
  return Datatypes::CompareSpec2Type(x0_);
}

#endif // INCLUDED_NAT_MODULE_FAMILY_RETURNS
