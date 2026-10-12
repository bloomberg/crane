#ifndef INCLUDED_MODULE_ALIAS_TARGET_HANDLING
#define INCLUDED_MODULE_ALIAS_TARGET_HANDLING

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
enum class Comparison;
enum class CompareSpecT;
template <typename A> struct Sig;
template <typename A> struct Sumor;
struct Uint;
struct Signed_int;
struct Uint0;
struct Signed_int0;
struct Uint1;
struct Signed_int1;

struct Little {
  static Uint double_(const Uint &d);
  static Uint succ_double(const Uint &d);
};

struct Coq_Little {
  static Uint0 double_(const Uint0 &d);
  static Uint0 succ_double(const Uint0 &d);
};

struct Bool {
  static Reflect iff_reflect(bool b);
};
enum class Reflect { REFLECTT, REFLECTF };
enum class Comparison { EQ, LT, GT };
enum class CompareSpecT { COMPEQT, COMPLTT, COMPGTT };
template <typename a = void> using CompSpecT = CompareSpecT;

struct Datatypes {
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

template <typename A> struct Sumor {
  // TYPES
  struct Inleft {
    A a0;
  };

  struct Inright {};

  using variant_t = std::variant<Inleft, Inright>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Sumor() {}

  explicit Sumor(Inleft _v) : v_(std::move(_v)) {}

  explicit Sumor(Inright _v) : v_(_v) {}

  template <typename CraneU>
  Sumor(const Sumor<CraneU> &_other)
      : v_([&]() -> variant_t {
          if (std::holds_alternative<typename Sumor<CraneU>::Inleft>(
                  _other.v())) {
            const auto &[a0] =
                std::get<typename Sumor<CraneU>::Inleft>(_other.v());
            return Inleft{[&]() -> A {
              if constexpr (crane_convertible<A, const CraneU &>) {
                return crane_convert<A>(a0);
              } else {
                throw std::logic_error("unreachable: inactive constructor "
                                       "field at this instantiation");
              }
            }()};
          } else {
            return Inright{};
          }
        }()) {}

  static Sumor<A> inleft(A a0) { return Sumor<A>(Inleft{std::move(a0)}); }

  static Sumor<A> inright() { return Sumor<A>(Inright{}); }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
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

  struct D14 {
    std::shared_ptr<Uint0> a0;
  };

  struct D13 {
    std::shared_ptr<Uint0> a0;
  };

  struct D17 {
    std::shared_ptr<Uint0> a0;
  };

  struct D15 {
    std::shared_ptr<Uint0> a0;
  };

  struct D18 {
    std::shared_ptr<Uint0> a0;
  };

  struct D16 {
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

  using variant_t = std::variant<Nil0, D10, D11, D12, D14, D13, D17, D15, D18,
                                 D16, D19, Da, Db, Dc, Dd, De, Df>;

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

  explicit Uint0(D14 _v) : v_(std::move(_v)) {}

  explicit Uint0(D13 _v) : v_(std::move(_v)) {}

  explicit Uint0(D17 _v) : v_(std::move(_v)) {}

  explicit Uint0(D15 _v) : v_(std::move(_v)) {}

  explicit Uint0(D18 _v) : v_(std::move(_v)) {}

  explicit Uint0(D16 _v) : v_(std::move(_v)) {}

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

  static Uint0 d14(Uint0 a0) {
    return Uint0(D14{std::make_shared<Uint0>(std::move(a0))});
  }

  static Uint0 d13(Uint0 a0) {
    return Uint0(D13{std::make_shared<Uint0>(std::move(a0))});
  }

  static Uint0 d17(Uint0 a0) {
    return Uint0(D17{std::make_shared<Uint0>(std::move(a0))});
  }

  static Uint0 d15(Uint0 a0) {
    return Uint0(D15{std::make_shared<Uint0>(std::move(a0))});
  }

  static Uint0 d18(Uint0 a0) {
    return Uint0(D18{std::make_shared<Uint0>(std::move(a0))});
  }

  static Uint0 d16(Uint0 a0) {
    return Uint0(D16{std::make_shared<Uint0>(std::move(a0))});
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
      if (auto *_alt = std::get_if<D14>(&_v)) {
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
      if (auto *_alt = std::get_if<D17>(&_v)) {
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
      if (auto *_alt = std::get_if<D18>(&_v)) {
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
    } else if (std::holds_alternative<typename Uint0::D14>(_sv.v())) {
      const auto &[a0] = std::get<typename Uint0::D14>(_sv.v());
      return Uint0::d14(*a0);
    } else if (std::holds_alternative<typename Uint0::D13>(_sv.v())) {
      const auto &[a0] = std::get<typename Uint0::D13>(_sv.v());
      return Uint0::d13(*a0);
    } else if (std::holds_alternative<typename Uint0::D17>(_sv.v())) {
      const auto &[a0] = std::get<typename Uint0::D17>(_sv.v());
      return Uint0::d17(*a0);
    } else if (std::holds_alternative<typename Uint0::D15>(_sv.v())) {
      const auto &[a0] = std::get<typename Uint0::D15>(_sv.v());
      return Uint0::d15(*a0);
    } else if (std::holds_alternative<typename Uint0::D18>(_sv.v())) {
      const auto &[a0] = std::get<typename Uint0::D18>(_sv.v());
      return Uint0::d18(*a0);
    } else if (std::holds_alternative<typename Uint0::D16>(_sv.v())) {
      const auto &[a0] = std::get<typename Uint0::D16>(_sv.v());
      return Uint0::d16(*a0);
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
      } else if (std::holds_alternative<typename Uint0::D14>(_sv.v())) {
        const auto &[a0] = std::get<typename Uint0::D14>(_sv.v());
        _loop_self = crane_raw(a0);
        _loop_d_ = Uint0::d14(std::move(_loop_d_));
      } else if (std::holds_alternative<typename Uint0::D13>(_sv.v())) {
        const auto &[a0] = std::get<typename Uint0::D13>(_sv.v());
        _loop_self = crane_raw(a0);
        _loop_d_ = Uint0::d13(std::move(_loop_d_));
      } else if (std::holds_alternative<typename Uint0::D17>(_sv.v())) {
        const auto &[a0] = std::get<typename Uint0::D17>(_sv.v());
        _loop_self = crane_raw(a0);
        _loop_d_ = Uint0::d17(std::move(_loop_d_));
      } else if (std::holds_alternative<typename Uint0::D15>(_sv.v())) {
        const auto &[a0] = std::get<typename Uint0::D15>(_sv.v());
        _loop_self = crane_raw(a0);
        _loop_d_ = Uint0::d15(std::move(_loop_d_));
      } else if (std::holds_alternative<typename Uint0::D18>(_sv.v())) {
        const auto &[a0] = std::get<typename Uint0::D18>(_sv.v());
        _loop_self = crane_raw(a0);
        _loop_d_ = Uint0::d18(std::move(_loop_d_));
      } else if (std::holds_alternative<typename Uint0::D16>(_sv.v())) {
        const auto &[a0] = std::get<typename Uint0::D16>(_sv.v());
        _loop_self = crane_raw(a0);
        _loop_d_ = Uint0::d16(std::move(_loop_d_));
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
      } else if (std::holds_alternative<typename Uint0::D14>(_sv0.v())) {
        const auto &[a00] = std::get<typename Uint0::D14>(_sv0.v());
        return Signed_int0::neg0(Uint0::d14(*a00));
      } else if (std::holds_alternative<typename Uint0::D13>(_sv0.v())) {
        const auto &[a00] = std::get<typename Uint0::D13>(_sv0.v());
        return Signed_int0::neg0(Uint0::d13(*a00));
      } else if (std::holds_alternative<typename Uint0::D17>(_sv0.v())) {
        const auto &[a00] = std::get<typename Uint0::D17>(_sv0.v());
        return Signed_int0::neg0(Uint0::d17(*a00));
      } else if (std::holds_alternative<typename Uint0::D15>(_sv0.v())) {
        const auto &[a00] = std::get<typename Uint0::D15>(_sv0.v());
        return Signed_int0::neg0(Uint0::d15(*a00));
      } else if (std::holds_alternative<typename Uint0::D18>(_sv0.v())) {
        const auto &[a00] = std::get<typename Uint0::D18>(_sv0.v());
        return Signed_int0::neg0(Uint0::d18(*a00));
      } else if (std::holds_alternative<typename Uint0::D16>(_sv0.v())) {
        const auto &[a00] = std::get<typename Uint0::D16>(_sv0.v());
        return Signed_int0::neg0(Uint0::d16(*a00));
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

struct Pos {
  static unsigned int succ(unsigned int x);
  static unsigned int pred_double(unsigned int x);

  struct mask {
    // TYPES
    struct IsNul {};

    struct IsPos {
      unsigned int a0;
    };

    struct IsNeg {};

    using variant_t = std::variant<IsNul, IsPos, IsNeg>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    mask() {}

    explicit mask(IsNul _v) : v_(_v) {}

    explicit mask(IsPos _v) : v_(std::move(_v)) {}

    explicit mask(IsNeg _v) : v_(_v) {}

    static mask isnul() { return mask(IsNul{}); }

    static mask ispos(unsigned int a0) { return mask(IsPos{a0}); }

    static mask isneg() { return mask(IsNeg{}); }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  static mask succ_double_mask(const mask &x);
  static mask double_mask(const mask &x);
  static mask double_pred_mask(unsigned int x);
  static mask sub_mask(unsigned int x, unsigned int y);
  static mask sub_mask_carry(unsigned int x, unsigned int y);

  template <typename T1, typename F0>
  static T1 iter(F0 &&f0, const T1 &x, unsigned int n) {
    if (n == 1u) {
      return f0(x);
    } else if (n % 2u != 0u) {
      unsigned int n_ = (n - 1u) / 2u;
      return f0(iter<T1>(f0, iter<T1>(f0, x, n_), n_));
    } else {
      unsigned int n_ = n / 2u;
      return iter<T1>(f0, iter<T1>(f0, x, n_), n_);
    }
  }

  static Comparison compare_cont(Comparison r, unsigned int x, unsigned int y);
  static Comparison compare(unsigned int x0_, unsigned int x1_);
  static bool leb(unsigned int x, unsigned int y);

  template <typename F0, typename F1>
  static std::pair<unsigned int, mask>
  sqrtrem_step(F0 &&f0, F1 &&g, std::pair<unsigned int, mask> p) {
    auto [s, y] = std::move(p);
    if (std::holds_alternative<typename mask::IsPos>(y.v_mut())) {
      auto &[a0] = std::get<typename mask::IsPos>(y.v_mut());
      unsigned int s_ = (2u * (2u * s) + 1u);
      unsigned int r_ = g(f0(std::move(a0)));
      if (leb(s_, r_)) {
        return std::make_pair((2u * s + 1u), sub_mask(r_, s_));
      } else {
        return std::make_pair((2u * s), mask::ispos(r_));
      }
    } else {
      return std::make_pair((2u * s), sub_mask(g(f0(1u)), (2u * (2u * 1u))));
    }
  }

  static std::pair<unsigned int, mask> sqrtrem(unsigned int p);
  static unsigned int sqrt(unsigned int p);
  static unsigned int Nsucc_double(unsigned int x);
  static unsigned int Ndouble(unsigned int n);
  static unsigned int lor(unsigned int p, unsigned int q);
  static unsigned int land(unsigned int p, unsigned int q);
  static unsigned int ldiff(unsigned int p, unsigned int q);
  static unsigned int lxor(unsigned int p, unsigned int q);
};

struct Coq_Pos {
  static unsigned int add_carry(unsigned int x, unsigned int y);
  static unsigned int pred_double(unsigned int x);
  static unsigned int pred_N(unsigned int x);

  template <typename T1, typename F0>
  static T1 iter(F0 &&f0, const T1 &x, unsigned int n) {
    if (n == 1u) {
      return f0(x);
    } else if (n % 2u != 0u) {
      unsigned int n_ = (n - 1u) / 2u;
      return f0(iter<T1>(f0, iter<T1>(f0, x, n_), n_));
    } else {
      unsigned int n_ = n / 2u;
      return iter<T1>(f0, iter<T1>(f0, x, n_), n_);
    }
  }

  static Comparison compare_cont(Comparison r, unsigned int x, unsigned int y);
  static Comparison compare(unsigned int x0_, unsigned int x1_);
  static unsigned int pow(unsigned int x, unsigned int x0_);
  static unsigned int square(unsigned int p);
  static uint64_t size_nat(unsigned int p);
  static unsigned int size(unsigned int p);
  static unsigned int gcdn(uint64_t n, unsigned int a, unsigned int b);
  static unsigned int gcd(unsigned int a, unsigned int b);
  static std::pair<unsigned int, std::pair<unsigned int, unsigned int>>
  ggcdn(uint64_t n, unsigned int a, unsigned int b);
  static std::pair<unsigned int, std::pair<unsigned int, unsigned int>>
  ggcd(unsigned int a, unsigned int b);
  static unsigned int shiftl(unsigned int p, unsigned int n);
  static bool testbit_nat(unsigned int p, uint64_t n);
  static bool testbit(unsigned int p, unsigned int n);
  static unsigned int of_uint_acc(const Uint &d, unsigned int acc);
  static unsigned int of_uint(const Uint &d);
  static unsigned int of_hex_uint_acc(const Uint0 &d, unsigned int acc);
  static unsigned int of_hex_uint(const Uint0 &d);
  static Uint to_little_uint(unsigned int p);
  static Uint to_uint(unsigned int p);
  static Uint0 to_little_hex_uint(unsigned int p);
  static Uint0 to_hex_uint(unsigned int p);
  static bool eq_dec(unsigned int p, unsigned int x0);

  template <typename T1>
  static T1 peano_rect(T1 a,
                       std::type_identity_t<crane::fn<T1(unsigned int, T1)>> f0,
                       unsigned int p) {
    crane::fn<T1(unsigned int)> f2 = [=](unsigned int _x0) -> T1 {
      return peano_rect<T1>(
          f0(1u, a),
          [=](unsigned int p0, const T1 &x) {
            return f0(((2u * p0) + 1u), f0((2u * p0), x));
          },
          _x0);
    };
    if (p == 1u) {
      return a;
    } else if (p % 2u != 0u) {
      unsigned int q = (p - 1u) / 2u;
      return f0((2u * q), f2(q));
    } else {
      unsigned int q = p / 2u;
      return f2(q);
    }
  }
};

struct N {
  static unsigned int succ_pos(unsigned int n);
  static Comparison compare(unsigned int n, unsigned int m);
  static std::pair<unsigned int, unsigned int> pos_div_eucl(unsigned int a,
                                                            unsigned int b);
  static unsigned int lor(unsigned int n, unsigned int m);
  static unsigned int land(unsigned int n, unsigned int m);
  static unsigned int ldiff(unsigned int n, unsigned int m);
  static unsigned int lxor(unsigned int n, unsigned int m);
  using t = unsigned int;
  static constexpr unsigned int zero = 0u;
  static constexpr unsigned int one = 1u;
  static constexpr unsigned int two = 2u;
  static unsigned int div2(unsigned int n);
  static bool even(unsigned int n);
  static bool odd(unsigned int n);
  static unsigned int pow(unsigned int n, unsigned int p);
  static unsigned int square(unsigned int n);
  static unsigned int log2(unsigned int n);
  static unsigned int size(unsigned int n);
  static uint64_t size_nat(unsigned int n);
  static std::pair<unsigned int, unsigned int> div_eucl(unsigned int a,
                                                        unsigned int b);
  static unsigned int gcd(unsigned int a, unsigned int b);
  static std::pair<unsigned int, std::pair<unsigned int, unsigned int>>
  ggcd(unsigned int a, unsigned int b);
  static std::pair<unsigned int, unsigned int> sqrtrem(unsigned int n);
  static unsigned int sqrt(unsigned int n);
  static unsigned int shiftl_nat(unsigned int a, uint64_t n);
  static unsigned int shiftr_nat(unsigned int a, uint64_t n);
  static unsigned int shiftl(unsigned int a, unsigned int n);
  static unsigned int shiftr(unsigned int a, unsigned int n);
  static bool testbit_nat(unsigned int a, uint64_t x0_);
  static bool testbit(unsigned int a, unsigned int n);

  template <typename T1, typename F1>
  static T1 iter(unsigned int n, F1 &&f0, T1 x) {
    if (n == 0u) {
      return x;
    } else {
      unsigned int p = n;
      return Pos::template iter<T1>(f0, std::move(x), p);
    }
  }

  static unsigned int of_uint(const Uint &x0_);
  static unsigned int of_hex_uint(const Uint0 &x0_);
  static unsigned int of_num_uint(const Uint1 &d);
  static std::optional<unsigned int> of_int(const Signed_int &d);
  static std::optional<unsigned int> of_hex_int(const Signed_int0 &d);
  static std::optional<unsigned int> of_num_int(const Signed_int1 &d);
  static Uint to_uint(unsigned int n);
  static Uint0 to_hex_uint(unsigned int n);
  static Uint1 to_num_uint(unsigned int n);
  static Uint1 to_num_hex_uint(unsigned int n);
  static Signed_int to_int(unsigned int n);
  static Signed_int0 to_hex_int(unsigned int n);
  static Signed_int1 to_num_int(unsigned int n);
  static Signed_int1 to_num_hex_int(unsigned int n);
  static bool eq_dec(unsigned int n, unsigned int m);
  static Sumor<Sig<unsigned int>> discr(unsigned int n);

  template <typename T1>
  static T1
  binary_rect(T1 f0, std::type_identity_t<crane::fn<T1(unsigned int, T1)>> f2,
              std::type_identity_t<crane::fn<T1(unsigned int, T1)>> fS2,
              unsigned int n) {
    crane::fn<T1(unsigned int, T1)> f2_ =
        [=, f2 = std::move(f2)](unsigned int p, const T1 &x) {
          return f2(p, x);
        };
    crane::fn<T1(unsigned int, T1)> fS2_ = [=](unsigned int p, const T1 &x) {
      return fS2(p, x);
    };
    if (n == 0u) {
      return f0;
    } else {
      unsigned int p = n;
      auto f1_impl = [&](auto &_self_f1, unsigned int p0) -> T1 {
        if (p0 == 1u) {
          return fS2(0u, f0);
        } else if (p0 % 2u != 0u) {
          unsigned int p1 = (p0 - 1u) / 2u;
          return fS2_(p1, _self_f1(_self_f1, p1));
        } else {
          unsigned int p1 = p0 / 2u;
          return f2_(p1, _self_f1(_self_f1, p1));
        }
      };
      auto f1 = [&](unsigned int p0) -> T1 { return f1_impl(f1_impl, p0); };
      return f1(p);
    }
  }

  template <typename T1, typename F1, typename F2>
  static T1 binary_rec(const T1 &x0_, F1 &&x1_, F2 &&x2_, unsigned int x3_) {
    return binary_rect<T1>(x0_, x1_, x2_, x3_);
  }

  template <typename T1>
  static T1 peano_rect(T1 f0,
                       std::type_identity_t<crane::fn<T1(unsigned int, T1)>> f1,
                       unsigned int n) {
    crane::fn<T1(unsigned int, T1)> f_ = [=](unsigned int p, const T1 &x) {
      return f1(p, x);
    };
    if (n == 0u) {
      return f0;
    } else {
      unsigned int p = n;
      return Coq_Pos::peano_rect(f1(0u, std::move(f0)), std::move(f_), p);
    }
  }

  template <typename T1, typename F1>
  static T1 peano_rec(const T1 &x0_, F1 &&x1_, unsigned int x2_) {
    return peano_rect<T1>(x0_, x1_, x2_);
  }

  template <typename T1, typename F1>
  static T1 recursion(const T1 &x0_, F1 &&x1_, unsigned int x2_) {
    return peano_rect<T1>(x0_, x1_, x2_);
  }

  static Reflect leb_spec0(unsigned int x, unsigned int y);
  static Reflect ltb_spec0(unsigned int x, unsigned int y);

  struct Private_OrderTac {
    struct IsTotal {};

    struct Tac {};
  };

  template <typename T1, typename T2, typename F2>
    requires std::is_invocable_r_v<T2, const F2 &, T1 &, crane::fn<T2(T1)>>
  static T2
  measure_right_induction(std::type_identity_t<crane::fn<unsigned int(T1)>> f0,
                          unsigned int, F2 &&iH, const T1 &x) {
    unsigned int t0 = f0(x);
    auto f1_impl = [=, f0 = std::move(f0)](auto &_self_f1, T1, T1 y) -> T2 {
      return iH(y, [=](const T1 &y_) {
        T1 y0 = f0(y_);
        return _self_f1(_self_f1, y0, y_);
      });
    };
    {
      T1 _lc1_x0 = t0;
      T1 _lc1_y = x;
      return f1_impl(f1_impl, std::move(_lc1_x0), std::move(_lc1_y));
    }
  }

  template <typename T1, typename T2, typename F0, typename F2>
  static T2 measure_left_induction(F0 &&f0, unsigned int _x, F2 &&iH,
                                   const T1 &x) {
    return measure_right_induction<T1, T2>(f0, _x, iH, x);
  }

  template <typename T1, typename T2, typename F0>
  static T2 measure_induction(
      F0 &&f0, std::type_identity_t<crane::fn<T2(T1, crane::fn<T2(T1)>)>> iH,
      const T1 &x) {
    return measure_right_induction<T1, T2>(
        f0, 0u,
        [=, iH = std::move(iH)](const T1 &y, crane::fn<T2(T1)> iH_) {
          return iH(y, [=](const T1 &y0) { return iH_(y0); });
        },
        x);
  }

  struct Private_Tac {};

  struct Private_Dec {
    template <typename T1, typename F2>
      requires std::is_invocable_r_v<T1, F2 &, unsigned int &, unsigned int,
                                     const T1 &>
    static T1 max_case_strong(unsigned int n, unsigned int m, F2 &&compat,
                              const T1 &hl, const T1 &hr) {
      CompareSpecT c = Datatypes::CompSpec2Type(n, m, compare(n, m));
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
    static T1 max_case(unsigned int n, unsigned int m, F2 &&x, const T1 &x0,
                       const T1 &x1) {
      return max_case_strong<T1>(
          n, m, x, [=]() { return x0; }(), [=]() { return x1; }());
    }

    static bool max_dec(unsigned int n, unsigned int m);

    template <typename T1, typename F2>
      requires std::is_invocable_r_v<T1, F2 &, unsigned int &, unsigned int,
                                     const T1 &>
    static T1 min_case_strong(unsigned int n, unsigned int m, F2 &&compat,
                              const T1 &hl, const T1 &hr) {
      CompareSpecT c = Datatypes::CompSpec2Type(n, m, compare(n, m));
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
    static T1 min_case(unsigned int n, unsigned int m, F2 &&x, const T1 &x0,
                       const T1 &x1) {
      return min_case_strong<T1>(
          n, m, x, [=]() { return x0; }(), [=]() { return x1; }());
    }

    static bool min_dec(unsigned int n, unsigned int m);
  };

  template <typename T1>
  static T1 max_case_strong(unsigned int n, unsigned int m, const T1 &x,
                            const T1 &x0) {
    return Private_Dec::template max_case_strong<T1>(
        n, m, [](unsigned int, unsigned int, T1 x1) { return x1; }, x, x0);
  }

  template <typename T1>
  static T1 max_case(unsigned int n, unsigned int m, const T1 &x,
                     const T1 &x0) {
    return max_case_strong<T1>(
        n, m, [=]() { return x; }(), [=]() { return x0; }());
  }

  static bool max_dec(unsigned int x0_, unsigned int x1_);

  template <typename T1>
  static T1 min_case_strong(unsigned int n, unsigned int m, const T1 &x,
                            const T1 &x0) {
    return Private_Dec::template min_case_strong<T1>(
        n, m, [](unsigned int, unsigned int, T1 x1) { return x1; }, x, x0);
  }

  template <typename T1>
  static T1 min_case(unsigned int n, unsigned int m, const T1 &x,
                     const T1 &x0) {
    return min_case_strong<T1>(
        n, m, [=]() { return x; }(), [=]() { return x0; }());
  }

  static bool min_dec(unsigned int x0_, unsigned int x1_);

  struct Private_NZPow {};

  struct Private_NZSqrt {};

  static unsigned int sqrt_up(unsigned int a);
  static unsigned int log2_up(unsigned int a);

  struct Private_NZGcdProp {};

  struct Private_NDivProp {
    struct Private_NZDiv {};
  };

  struct Div0 {};

  struct Private_NLcmProp {
    static unsigned int lcm(unsigned int a, unsigned int b);
  };

  static unsigned int lcm(unsigned int a, unsigned int b);

  struct Lcm0 {};

  static Reflect eqb_spec(unsigned int x, unsigned int y);
  static unsigned int b2n(bool b);
  static unsigned int setbit(unsigned int a, unsigned int n);
  static unsigned int clearbit(unsigned int a, unsigned int n);
  static unsigned int ones(unsigned int n);
  static unsigned int lnot(unsigned int a, unsigned int n);
};

struct ModuleAliasTargetHandling {
  using NN = N;
  static inline const unsigned int mapped = NN::max(3u, 4u);

  struct T_Mod {
    struct T {
      // TYPES
      struct A {};

      struct B {
        uint64_t a0;
      };

      using variant_t = std::variant<A, B>;

    private:
      // DATA
      variant_t v_;

    public:
      // CREATORS
      T() {}

      explicit T(A _v) : v_(_v) {}

      explicit T(B _v) : v_(std::move(_v)) {}

      static T a() { return T(A{}); }

      static T b(uint64_t a0) { return T(B{a0}); }

      // MANIPULATORS
      inline variant_t &v_mut() { return v_; }

      // ACCESSORS
      const variant_t &v() const { return v_; }

      uint64_t f() const {
        if (std::holds_alternative<typename T::A>(this->v())) {
          return UINT64_C(0);
        } else {
          const auto &[a0] = std::get<typename T::B>(this->v());
          return a0;
        }
      }

      template <typename T1, typename F1> T1 T_rec(T1 f0, F1 &&f1) const {
        return this->template T_rect<T1>(std::move(f0), f1);
      }

      template <typename T1, typename F1>
        requires std::is_invocable_r_v<T1, F1 &, const uint64_t &>
      T1 T_rect(T1 f0, F1 &&f1) const {
        if (std::holds_alternative<typename T::A>(this->v())) {
          return f0;
        } else {
          const auto &[a0] = std::get<typename T::B>(this->v());
          return f1(a0);
        }
      }
    };
  };

  using U = T_Mod;
  static inline const uint64_t methodified =
      (U::f(T_Mod::T::b(UINT64_C(3))) + U::f(U::T::a()));
};

template <typename T1>
CompSpecT<T1> Datatypes::CompSpec2Type(const T1 &, const T1 &, Comparison x0_) {
  return Datatypes::CompareSpec2Type(x0_);
}

#endif // INCLUDED_MODULE_ALIAS_TARGET_HANDLING
