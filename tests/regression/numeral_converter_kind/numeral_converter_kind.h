#ifndef INCLUDED_NUMERAL_CONVERTER_KIND
#define INCLUDED_NUMERAL_CONVERTER_KIND

#include "crane_fn.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <optional>
#include <utility>
#include <variant>

struct Uint;
struct Signed_int;
struct Uint0;
struct Signed_int0;
struct Signed_int1;

struct Nat {
  static uint64_t tail_add(uint64_t n, uint64_t m);
  static uint64_t tail_addmul(uint64_t r, uint64_t n, uint64_t m);
  static uint64_t tail_mul(uint64_t n, uint64_t m);
  static uint64_t of_uint_acc(const Uint &d, uint64_t acc);
  static uint64_t of_uint(const Uint &d);
  static uint64_t of_hex_uint_acc(const Uint0 &d, uint64_t acc);
  static uint64_t of_hex_uint(const Uint0 &d);
  static std::optional<uint64_t> of_int(const Signed_int &d);
  static std::optional<uint64_t> of_hex_int(const Signed_int0 &d);
  static std::optional<uint64_t> of_num_int(const Signed_int1 &d);
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

struct NumeralConverterKind {
  static constexpr int64_t z_minus_one = INT64_C(-1);
  static constexpr int64_t z_minus_ten_hex = INT64_C(-10);
  static constexpr int64_t z_plus_twelve = INT64_C(12);
  static constexpr int64_t z_uint = INT64_C(42);
  static constexpr uint64_t nat_big = UINT64_C(10000);
  static inline const std::optional<uint64_t> nat_of_pos = Nat::of_num_int(
      Signed_int1::intdecimal(Signed_int::pos(Uint::d7(Uint::nil()))));

  static inline const std::optional<uint64_t> nat_of_neg = Nat::of_num_int(
      Signed_int1::intdecimal(Signed_int::neg(Uint::d7(Uint::nil()))));
};

#endif // INCLUDED_NUMERAL_CONVERTER_KIND
