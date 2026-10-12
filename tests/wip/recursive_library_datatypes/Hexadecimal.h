#ifndef INCLUDED_HEXADECIMAL
#define INCLUDED_HEXADECIMAL

#include "crane_fn.h"
#include "small_vector.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <utility>
#include <variant>

#include "Datatypes.h"
#include "Decimal.h"
#include "Specif.h"

struct Uint;
struct Signed_int;
struct Hexadecimal;

struct Little {
  static uint succ(const uint &d);
  static uint double_(const uint &d);
  static uint succ_double(const uint &d);
};

struct Uint {
  // TYPES
  struct Nil {};

  struct D0 {
    std::shared_ptr<uint> a0;
  };

  struct D1 {
    std::shared_ptr<uint> a0;
  };

  struct D2 {
    std::shared_ptr<uint> a0;
  };

  struct D3 {
    std::shared_ptr<uint> a0;
  };

  struct D4 {
    std::shared_ptr<uint> a0;
  };

  struct D5 {
    std::shared_ptr<uint> a0;
  };

  struct D6 {
    std::shared_ptr<uint> a0;
  };

  struct D7 {
    std::shared_ptr<uint> a0;
  };

  struct D8 {
    std::shared_ptr<uint> a0;
  };

  struct D9 {
    std::shared_ptr<uint> a0;
  };

  struct Da {
    std::shared_ptr<uint> a0;
  };

  struct Db {
    std::shared_ptr<uint> a0;
  };

  struct Dc {
    std::shared_ptr<uint> a0;
  };

  struct Dd {
    std::shared_ptr<uint> a0;
  };

  struct De {
    std::shared_ptr<uint> a0;
  };

  struct Df {
    std::shared_ptr<uint> a0;
  };

  using variant_t = std::variant<Nil, D0, D1, D2, D3, D4, D5, D6, D7, D8, D9,
                                 Da, Db, Dc, Dd, De, Df>;

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

  explicit Uint(Da _v) : v_(std::move(_v)) {}

  explicit Uint(Db _v) : v_(std::move(_v)) {}

  explicit Uint(Dc _v) : v_(std::move(_v)) {}

  explicit Uint(Dd _v) : v_(std::move(_v)) {}

  explicit Uint(De _v) : v_(std::move(_v)) {}

  explicit Uint(Df _v) : v_(std::move(_v)) {}

  static uint nil() { return uint(Nil{}); }

  static uint d0(uint a0) {
    return uint(D0{std::make_shared<uint>(std::move(a0))});
  }

  static uint d1(uint a0) {
    return uint(D1{std::make_shared<uint>(std::move(a0))});
  }

  static uint d2(uint a0) {
    return uint(D2{std::make_shared<uint>(std::move(a0))});
  }

  static uint d3(uint a0) {
    return uint(D3{std::make_shared<uint>(std::move(a0))});
  }

  static uint d4(uint a0) {
    return uint(D4{std::make_shared<uint>(std::move(a0))});
  }

  static uint d5(uint a0) {
    return uint(D5{std::make_shared<uint>(std::move(a0))});
  }

  static uint d6(uint a0) {
    return uint(D6{std::make_shared<uint>(std::move(a0))});
  }

  static uint d7(uint a0) {
    return uint(D7{std::make_shared<uint>(std::move(a0))});
  }

  static uint d8(uint a0) {
    return uint(D8{std::make_shared<uint>(std::move(a0))});
  }

  static uint d9(uint a0) {
    return uint(D9{std::make_shared<uint>(std::move(a0))});
  }

  static uint da(uint a0) {
    return uint(Da{std::make_shared<uint>(std::move(a0))});
  }

  static uint db(uint a0) {
    return uint(Db{std::make_shared<uint>(std::move(a0))});
  }

  static uint dc(uint a0) {
    return uint(Dc{std::make_shared<uint>(std::move(a0))});
  }

  static uint dd(uint a0) {
    return uint(Dd{std::make_shared<uint>(std::move(a0))});
  }

  static uint de(uint a0) {
    return uint(De{std::make_shared<uint>(std::move(a0))});
  }

  static uint df(uint a0) {
    return uint(Df{std::make_shared<uint>(std::move(a0))});
  }

  // MANIPULATORS
  ~Uint() {
    auto _next = [&](variant_t &_v) -> std::shared_ptr<uint> {
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
    std::shared_ptr<uint> _cur = _next(v_mut());
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

  template <typename T1, typename F1, typename F2, typename F3, typename F4,
            typename F5, typename F6, typename F7, typename F8, typename F9,
            typename F10, typename F11, typename F12, typename F13,
            typename F14, typename F15, typename F16>
  T1 uint_rect(T1 f, F1 &&f0, F2 &&f1, F3 &&f2, F4 &&f3, F5 &&f4, F6 &&f5,
               F7 &&f6, F8 &&f7, F9 &&f8, F10 &&f9, F11 &&f10, F12 &&f11,
               F13 &&f12, F14 &&f13, F15 &&f14, F16 &&f15) const {
    const uint *_self = this;

    /// CraneEnter: captures varying parameters for each recursive call.
    struct CraneEnter {
      const uint *_self;
    };

    /// CraneCont_D0: saves [a0], resumes after recursive call, then processes
    /// rest.
    struct CraneCont_D0 {
      std::shared_ptr<uint> a0;
    };

    /// CraneCont_D1: saves [a0], resumes after recursive call, then processes
    /// rest.
    struct CraneCont_D1 {
      std::shared_ptr<uint> a0;
    };

    /// CraneCont_D2: saves [a0], resumes after recursive call, then processes
    /// rest.
    struct CraneCont_D2 {
      std::shared_ptr<uint> a0;
    };

    /// CraneCont_D3: saves [a0], resumes after recursive call, then processes
    /// rest.
    struct CraneCont_D3 {
      std::shared_ptr<uint> a0;
    };

    /// CraneCont_D4: saves [a0], resumes after recursive call, then processes
    /// rest.
    struct CraneCont_D4 {
      std::shared_ptr<uint> a0;
    };

    /// CraneCont_D5: saves [a0], resumes after recursive call, then processes
    /// rest.
    struct CraneCont_D5 {
      std::shared_ptr<uint> a0;
    };

    /// CraneCont_D6: saves [a0], resumes after recursive call, then processes
    /// rest.
    struct CraneCont_D6 {
      std::shared_ptr<uint> a0;
    };

    /// CraneCont_D7: saves [a0], resumes after recursive call, then processes
    /// rest.
    struct CraneCont_D7 {
      std::shared_ptr<uint> a0;
    };

    /// CraneCont_D8: saves [a0], resumes after recursive call, then processes
    /// rest.
    struct CraneCont_D8 {
      std::shared_ptr<uint> a0;
    };

    /// CraneCont_D9: saves [a0], resumes after recursive call, then processes
    /// rest.
    struct CraneCont_D9 {
      std::shared_ptr<uint> a0;
    };

    /// CraneCont_Da: saves [a0], resumes after recursive call, then processes
    /// rest.
    struct CraneCont_Da {
      std::shared_ptr<uint> a0;
    };

    /// CraneCont_Db: saves [a0], resumes after recursive call, then processes
    /// rest.
    struct CraneCont_Db {
      std::shared_ptr<uint> a0;
    };

    /// CraneCont_Dc: saves [a0], resumes after recursive call, then processes
    /// rest.
    struct CraneCont_Dc {
      std::shared_ptr<uint> a0;
    };

    /// CraneCont_Dd: saves [a0], resumes after recursive call, then processes
    /// rest.
    struct CraneCont_Dd {
      std::shared_ptr<uint> a0;
    };

    /// CraneCont_De: saves [a0], resumes after recursive call, then processes
    /// rest.
    struct CraneCont_De {
      std::shared_ptr<uint> a0;
    };

    /// CraneCont_Df: saves [a0], resumes after recursive call, then processes
    /// rest.
    struct CraneCont_Df {
      std::shared_ptr<uint> a0;
    };

    using CraneFrame =
        std::variant<CraneEnter, CraneCont_D0, CraneCont_D1, CraneCont_D2,
                     CraneCont_D3, CraneCont_D4, CraneCont_D5, CraneCont_D6,
                     CraneCont_D7, CraneCont_D8, CraneCont_D9, CraneCont_Da,
                     CraneCont_Db, CraneCont_Dc, CraneCont_Dd, CraneCont_De,
                     CraneCont_Df>;
    T1 _result{};
    crane::small_vector<CraneFrame> _stack;
    _stack.emplace_back(CraneEnter{_self});
    /// Loopified uint_rect: CraneEnter -> CraneCont_D0 -> CraneCont_D1 ->
    /// CraneCont_D2 -> CraneCont_D3 -> CraneCont_D4 -> CraneCont_D5 ->
    /// CraneCont_D6 -> CraneCont_D7 -> CraneCont_D8 -> CraneCont_D9 ->
    /// CraneCont_Da -> CraneCont_Db -> CraneCont_Dc -> CraneCont_Dd ->
    /// CraneCont_De -> CraneCont_Df.
    while (!_stack.empty()) {
      CraneFrame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<CraneEnter>(_frame)) {
        auto _f = std::move(std::get<CraneEnter>(_frame));
        const uint *_self = _f._self;
        auto &&_sv = *_self;
        if (std::holds_alternative<typename uint::Nil>(_sv.v())) {
          _result = f;
        } else if (std::holds_alternative<typename uint::D0>(_sv.v())) {
          const auto &[a0] = std::get<typename uint::D0>(_sv.v());
          _stack.emplace_back(CraneCont_D0{a0});
          _stack.emplace_back(CraneEnter{crane_raw(a0)});
        } else if (std::holds_alternative<typename uint::D1>(_sv.v())) {
          const auto &[a0] = std::get<typename uint::D1>(_sv.v());
          _stack.emplace_back(CraneCont_D1{a0});
          _stack.emplace_back(CraneEnter{crane_raw(a0)});
        } else if (std::holds_alternative<typename uint::D2>(_sv.v())) {
          const auto &[a0] = std::get<typename uint::D2>(_sv.v());
          _stack.emplace_back(CraneCont_D2{a0});
          _stack.emplace_back(CraneEnter{crane_raw(a0)});
        } else if (std::holds_alternative<typename uint::D3>(_sv.v())) {
          const auto &[a0] = std::get<typename uint::D3>(_sv.v());
          _stack.emplace_back(CraneCont_D3{a0});
          _stack.emplace_back(CraneEnter{crane_raw(a0)});
        } else if (std::holds_alternative<typename uint::D4>(_sv.v())) {
          const auto &[a0] = std::get<typename uint::D4>(_sv.v());
          _stack.emplace_back(CraneCont_D4{a0});
          _stack.emplace_back(CraneEnter{crane_raw(a0)});
        } else if (std::holds_alternative<typename uint::D5>(_sv.v())) {
          const auto &[a0] = std::get<typename uint::D5>(_sv.v());
          _stack.emplace_back(CraneCont_D5{a0});
          _stack.emplace_back(CraneEnter{crane_raw(a0)});
        } else if (std::holds_alternative<typename uint::D6>(_sv.v())) {
          const auto &[a0] = std::get<typename uint::D6>(_sv.v());
          _stack.emplace_back(CraneCont_D6{a0});
          _stack.emplace_back(CraneEnter{crane_raw(a0)});
        } else if (std::holds_alternative<typename uint::D7>(_sv.v())) {
          const auto &[a0] = std::get<typename uint::D7>(_sv.v());
          _stack.emplace_back(CraneCont_D7{a0});
          _stack.emplace_back(CraneEnter{crane_raw(a0)});
        } else if (std::holds_alternative<typename uint::D8>(_sv.v())) {
          const auto &[a0] = std::get<typename uint::D8>(_sv.v());
          _stack.emplace_back(CraneCont_D8{a0});
          _stack.emplace_back(CraneEnter{crane_raw(a0)});
        } else if (std::holds_alternative<typename uint::D9>(_sv.v())) {
          const auto &[a0] = std::get<typename uint::D9>(_sv.v());
          _stack.emplace_back(CraneCont_D9{a0});
          _stack.emplace_back(CraneEnter{crane_raw(a0)});
        } else if (std::holds_alternative<typename uint::Da>(_sv.v())) {
          const auto &[a0] = std::get<typename uint::Da>(_sv.v());
          _stack.emplace_back(CraneCont_Da{a0});
          _stack.emplace_back(CraneEnter{crane_raw(a0)});
        } else if (std::holds_alternative<typename uint::Db>(_sv.v())) {
          const auto &[a0] = std::get<typename uint::Db>(_sv.v());
          _stack.emplace_back(CraneCont_Db{a0});
          _stack.emplace_back(CraneEnter{crane_raw(a0)});
        } else if (std::holds_alternative<typename uint::Dc>(_sv.v())) {
          const auto &[a0] = std::get<typename uint::Dc>(_sv.v());
          _stack.emplace_back(CraneCont_Dc{a0});
          _stack.emplace_back(CraneEnter{crane_raw(a0)});
        } else if (std::holds_alternative<typename uint::Dd>(_sv.v())) {
          const auto &[a0] = std::get<typename uint::Dd>(_sv.v());
          _stack.emplace_back(CraneCont_Dd{a0});
          _stack.emplace_back(CraneEnter{crane_raw(a0)});
        } else if (std::holds_alternative<typename uint::De>(_sv.v())) {
          const auto &[a0] = std::get<typename uint::De>(_sv.v());
          _stack.emplace_back(CraneCont_De{a0});
          _stack.emplace_back(CraneEnter{crane_raw(a0)});
        } else {
          const auto &[a0] = std::get<typename uint::Df>(_sv.v());
          _stack.emplace_back(CraneCont_Df{a0});
          _stack.emplace_back(CraneEnter{crane_raw(a0)});
        }
      } else if (std::holds_alternative<CraneCont_D0>(_frame)) {
        auto _f = std::move(std::get<CraneCont_D0>(_frame));
        std::shared_ptr<uint> a0 = std::move(_f.a0);
        _result = f0(*a0, std::move(_result));
      } else if (std::holds_alternative<CraneCont_D1>(_frame)) {
        auto _f = std::move(std::get<CraneCont_D1>(_frame));
        std::shared_ptr<uint> a0 = std::move(_f.a0);
        _result = f1(*a0, std::move(_result));
      } else if (std::holds_alternative<CraneCont_D2>(_frame)) {
        auto _f = std::move(std::get<CraneCont_D2>(_frame));
        std::shared_ptr<uint> a0 = std::move(_f.a0);
        _result = f2(*a0, std::move(_result));
      } else if (std::holds_alternative<CraneCont_D3>(_frame)) {
        auto _f = std::move(std::get<CraneCont_D3>(_frame));
        std::shared_ptr<uint> a0 = std::move(_f.a0);
        _result = f3(*a0, std::move(_result));
      } else if (std::holds_alternative<CraneCont_D4>(_frame)) {
        auto _f = std::move(std::get<CraneCont_D4>(_frame));
        std::shared_ptr<uint> a0 = std::move(_f.a0);
        _result = f4(*a0, std::move(_result));
      } else if (std::holds_alternative<CraneCont_D5>(_frame)) {
        auto _f = std::move(std::get<CraneCont_D5>(_frame));
        std::shared_ptr<uint> a0 = std::move(_f.a0);
        _result = f5(*a0, std::move(_result));
      } else if (std::holds_alternative<CraneCont_D6>(_frame)) {
        auto _f = std::move(std::get<CraneCont_D6>(_frame));
        std::shared_ptr<uint> a0 = std::move(_f.a0);
        _result = f6(*a0, std::move(_result));
      } else if (std::holds_alternative<CraneCont_D7>(_frame)) {
        auto _f = std::move(std::get<CraneCont_D7>(_frame));
        std::shared_ptr<uint> a0 = std::move(_f.a0);
        _result = f7(*a0, std::move(_result));
      } else if (std::holds_alternative<CraneCont_D8>(_frame)) {
        auto _f = std::move(std::get<CraneCont_D8>(_frame));
        std::shared_ptr<uint> a0 = std::move(_f.a0);
        _result = f8(*a0, std::move(_result));
      } else if (std::holds_alternative<CraneCont_D9>(_frame)) {
        auto _f = std::move(std::get<CraneCont_D9>(_frame));
        std::shared_ptr<uint> a0 = std::move(_f.a0);
        _result = f9(*a0, std::move(_result));
      } else if (std::holds_alternative<CraneCont_Da>(_frame)) {
        auto _f = std::move(std::get<CraneCont_Da>(_frame));
        std::shared_ptr<uint> a0 = std::move(_f.a0);
        _result = f10(*a0, std::move(_result));
      } else if (std::holds_alternative<CraneCont_Db>(_frame)) {
        auto _f = std::move(std::get<CraneCont_Db>(_frame));
        std::shared_ptr<uint> a0 = std::move(_f.a0);
        _result = f11(*a0, std::move(_result));
      } else if (std::holds_alternative<CraneCont_Dc>(_frame)) {
        auto _f = std::move(std::get<CraneCont_Dc>(_frame));
        std::shared_ptr<uint> a0 = std::move(_f.a0);
        _result = f12(*a0, std::move(_result));
      } else if (std::holds_alternative<CraneCont_Dd>(_frame)) {
        auto _f = std::move(std::get<CraneCont_Dd>(_frame));
        std::shared_ptr<uint> a0 = std::move(_f.a0);
        _result = f13(*a0, std::move(_result));
      } else if (std::holds_alternative<CraneCont_De>(_frame)) {
        auto _f = std::move(std::get<CraneCont_De>(_frame));
        std::shared_ptr<uint> a0 = std::move(_f.a0);
        _result = f14(*a0, std::move(_result));
      } else {
        auto _f = std::move(std::get<CraneCont_Df>(_frame));
        std::shared_ptr<uint> a0 = std::move(_f.a0);
        _result = f15(*a0, std::move(_result));
      }
    }
    return _result;
  }

  template <typename T1, typename F1, typename F2, typename F3, typename F4,
            typename F5, typename F6, typename F7, typename F8, typename F9,
            typename F10, typename F11, typename F12, typename F13,
            typename F14, typename F15, typename F16>
  T1 uint_rec(T1 f, F1 &&f0, F2 &&f1, F3 &&f2, F4 &&f3, F5 &&f4, F6 &&f5,
              F7 &&f6, F8 &&f7, F9 &&f8, F10 &&f9, F11 &&f10, F12 &&f11,
              F13 &&f12, F14 &&f13, F15 &&f14, F16 &&f15) const {
    return this->template uint_rect<T1>(std::move(f), f0, f1, f2, f3, f4, f5,
                                        f6, f7, f8, f9, f10, f11, f12, f13, f14,
                                        f15);
  }

  bool uint_beq(const uint &y) const {
    const uint *_loop_self = this;
    const uint *_loop_y = &y;
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename uint::Nil>(_sv.v())) {
        if (std::holds_alternative<typename uint::Nil>(_loop_y->v())) {
          return true;
        } else {
          return false;
        }
      } else if (std::holds_alternative<typename uint::D0>(_sv.v())) {
        const auto &[a0] = std::get<typename uint::D0>(_sv.v());
        if (std::holds_alternative<typename uint::D0>(_loop_y->v())) {
          const auto &[a00] = std::get<typename uint::D0>(_loop_y->v());
          _loop_self = crane_raw(a0);
          _loop_y = crane_raw(a00);
        } else {
          return false;
        }
      } else if (std::holds_alternative<typename uint::D1>(_sv.v())) {
        const auto &[a0] = std::get<typename uint::D1>(_sv.v());
        if (std::holds_alternative<typename uint::D1>(_loop_y->v())) {
          const auto &[a00] = std::get<typename uint::D1>(_loop_y->v());
          _loop_self = crane_raw(a0);
          _loop_y = crane_raw(a00);
        } else {
          return false;
        }
      } else if (std::holds_alternative<typename uint::D2>(_sv.v())) {
        const auto &[a0] = std::get<typename uint::D2>(_sv.v());
        if (std::holds_alternative<typename uint::D2>(_loop_y->v())) {
          const auto &[a00] = std::get<typename uint::D2>(_loop_y->v());
          _loop_self = crane_raw(a0);
          _loop_y = crane_raw(a00);
        } else {
          return false;
        }
      } else if (std::holds_alternative<typename uint::D3>(_sv.v())) {
        const auto &[a0] = std::get<typename uint::D3>(_sv.v());
        if (std::holds_alternative<typename uint::D3>(_loop_y->v())) {
          const auto &[a00] = std::get<typename uint::D3>(_loop_y->v());
          _loop_self = crane_raw(a0);
          _loop_y = crane_raw(a00);
        } else {
          return false;
        }
      } else if (std::holds_alternative<typename uint::D4>(_sv.v())) {
        const auto &[a0] = std::get<typename uint::D4>(_sv.v());
        if (std::holds_alternative<typename uint::D4>(_loop_y->v())) {
          const auto &[a00] = std::get<typename uint::D4>(_loop_y->v());
          _loop_self = crane_raw(a0);
          _loop_y = crane_raw(a00);
        } else {
          return false;
        }
      } else if (std::holds_alternative<typename uint::D5>(_sv.v())) {
        const auto &[a0] = std::get<typename uint::D5>(_sv.v());
        if (std::holds_alternative<typename uint::D5>(_loop_y->v())) {
          const auto &[a00] = std::get<typename uint::D5>(_loop_y->v());
          _loop_self = crane_raw(a0);
          _loop_y = crane_raw(a00);
        } else {
          return false;
        }
      } else if (std::holds_alternative<typename uint::D6>(_sv.v())) {
        const auto &[a0] = std::get<typename uint::D6>(_sv.v());
        if (std::holds_alternative<typename uint::D6>(_loop_y->v())) {
          const auto &[a00] = std::get<typename uint::D6>(_loop_y->v());
          _loop_self = crane_raw(a0);
          _loop_y = crane_raw(a00);
        } else {
          return false;
        }
      } else if (std::holds_alternative<typename uint::D7>(_sv.v())) {
        const auto &[a0] = std::get<typename uint::D7>(_sv.v());
        if (std::holds_alternative<typename uint::D7>(_loop_y->v())) {
          const auto &[a00] = std::get<typename uint::D7>(_loop_y->v());
          _loop_self = crane_raw(a0);
          _loop_y = crane_raw(a00);
        } else {
          return false;
        }
      } else if (std::holds_alternative<typename uint::D8>(_sv.v())) {
        const auto &[a0] = std::get<typename uint::D8>(_sv.v());
        if (std::holds_alternative<typename uint::D8>(_loop_y->v())) {
          const auto &[a00] = std::get<typename uint::D8>(_loop_y->v());
          _loop_self = crane_raw(a0);
          _loop_y = crane_raw(a00);
        } else {
          return false;
        }
      } else if (std::holds_alternative<typename uint::D9>(_sv.v())) {
        const auto &[a0] = std::get<typename uint::D9>(_sv.v());
        if (std::holds_alternative<typename uint::D9>(_loop_y->v())) {
          const auto &[a00] = std::get<typename uint::D9>(_loop_y->v());
          _loop_self = crane_raw(a0);
          _loop_y = crane_raw(a00);
        } else {
          return false;
        }
      } else if (std::holds_alternative<typename uint::Da>(_sv.v())) {
        const auto &[a0] = std::get<typename uint::Da>(_sv.v());
        if (std::holds_alternative<typename uint::Da>(_loop_y->v())) {
          const auto &[a00] = std::get<typename uint::Da>(_loop_y->v());
          _loop_self = crane_raw(a0);
          _loop_y = crane_raw(a00);
        } else {
          return false;
        }
      } else if (std::holds_alternative<typename uint::Db>(_sv.v())) {
        const auto &[a0] = std::get<typename uint::Db>(_sv.v());
        if (std::holds_alternative<typename uint::Db>(_loop_y->v())) {
          const auto &[a00] = std::get<typename uint::Db>(_loop_y->v());
          _loop_self = crane_raw(a0);
          _loop_y = crane_raw(a00);
        } else {
          return false;
        }
      } else if (std::holds_alternative<typename uint::Dc>(_sv.v())) {
        const auto &[a0] = std::get<typename uint::Dc>(_sv.v());
        if (std::holds_alternative<typename uint::Dc>(_loop_y->v())) {
          const auto &[a00] = std::get<typename uint::Dc>(_loop_y->v());
          _loop_self = crane_raw(a0);
          _loop_y = crane_raw(a00);
        } else {
          return false;
        }
      } else if (std::holds_alternative<typename uint::Dd>(_sv.v())) {
        const auto &[a0] = std::get<typename uint::Dd>(_sv.v());
        if (std::holds_alternative<typename uint::Dd>(_loop_y->v())) {
          const auto &[a00] = std::get<typename uint::Dd>(_loop_y->v());
          _loop_self = crane_raw(a0);
          _loop_y = crane_raw(a00);
        } else {
          return false;
        }
      } else if (std::holds_alternative<typename uint::De>(_sv.v())) {
        const auto &[a0] = std::get<typename uint::De>(_sv.v());
        if (std::holds_alternative<typename uint::De>(_loop_y->v())) {
          const auto &[a00] = std::get<typename uint::De>(_loop_y->v());
          _loop_self = crane_raw(a0);
          _loop_y = crane_raw(a00);
        } else {
          return false;
        }
      } else {
        const auto &[a0] = std::get<typename uint::Df>(_sv.v());
        if (std::holds_alternative<typename uint::Df>(_loop_y->v())) {
          const auto &[a00] = std::get<typename uint::Df>(_loop_y->v());
          _loop_self = crane_raw(a0);
          _loop_y = crane_raw(a00);
        } else {
          return false;
        }
      }
    }
  }

  bool uint_eq_dec(const uint &y) const {
    bool h;
    bool b = this->uint_beq(y);
    if (b) {
      h = true;
    } else {
      h = false;
    }
    if (h) {
      return true;
    } else {
      return false;
    }
  }

  uint64_t nb_digits() const {
    const uint *_self = this;

    /// CraneEnter: captures varying parameters for each recursive call.
    struct CraneEnter {
      const uint *_self;
    };

    /// CraneCont_D0: resumes after recursive call, then processes rest.
    struct CraneCont_D0 {};

    /// CraneCont_D1: resumes after recursive call, then processes rest.
    struct CraneCont_D1 {};

    /// CraneCont_D2: resumes after recursive call, then processes rest.
    struct CraneCont_D2 {};

    /// CraneCont_D3: resumes after recursive call, then processes rest.
    struct CraneCont_D3 {};

    /// CraneCont_D4: resumes after recursive call, then processes rest.
    struct CraneCont_D4 {};

    /// CraneCont_D5: resumes after recursive call, then processes rest.
    struct CraneCont_D5 {};

    /// CraneCont_D6: resumes after recursive call, then processes rest.
    struct CraneCont_D6 {};

    /// CraneCont_D7: resumes after recursive call, then processes rest.
    struct CraneCont_D7 {};

    /// CraneCont_D8: resumes after recursive call, then processes rest.
    struct CraneCont_D8 {};

    /// CraneCont_D9: resumes after recursive call, then processes rest.
    struct CraneCont_D9 {};

    /// CraneCont_Da: resumes after recursive call, then processes rest.
    struct CraneCont_Da {};

    /// CraneCont_Db: resumes after recursive call, then processes rest.
    struct CraneCont_Db {};

    /// CraneCont_Dc: resumes after recursive call, then processes rest.
    struct CraneCont_Dc {};

    /// CraneCont_Dd: resumes after recursive call, then processes rest.
    struct CraneCont_Dd {};

    /// CraneCont_De: resumes after recursive call, then processes rest.
    struct CraneCont_De {};

    /// CraneCont_Df: resumes after recursive call, then processes rest.
    struct CraneCont_Df {};

    using CraneFrame =
        std::variant<CraneEnter, CraneCont_D0, CraneCont_D1, CraneCont_D2,
                     CraneCont_D3, CraneCont_D4, CraneCont_D5, CraneCont_D6,
                     CraneCont_D7, CraneCont_D8, CraneCont_D9, CraneCont_Da,
                     CraneCont_Db, CraneCont_Dc, CraneCont_Dd, CraneCont_De,
                     CraneCont_Df>;
    uint64_t _result{};
    crane::small_vector<CraneFrame> _stack;
    _stack.emplace_back(CraneEnter{_self});
    /// Loopified nb_digits: CraneEnter -> CraneCont_D0 -> CraneCont_D1 ->
    /// CraneCont_D2 -> CraneCont_D3 -> CraneCont_D4 -> CraneCont_D5 ->
    /// CraneCont_D6 -> CraneCont_D7 -> CraneCont_D8 -> CraneCont_D9 ->
    /// CraneCont_Da -> CraneCont_Db -> CraneCont_Dc -> CraneCont_Dd ->
    /// CraneCont_De -> CraneCont_Df.
    while (!_stack.empty()) {
      CraneFrame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<CraneEnter>(_frame)) {
        auto _f = std::move(std::get<CraneEnter>(_frame));
        const uint *_self = _f._self;
        auto &&_sv = *_self;
        if (std::holds_alternative<typename uint::Nil>(_sv.v())) {
          _result = UINT64_C(0);
        } else if (std::holds_alternative<typename uint::D0>(_sv.v())) {
          const auto &[a0] = std::get<typename uint::D0>(_sv.v());
          _stack.emplace_back(CraneCont_D0{});
          _stack.emplace_back(CraneEnter{crane_raw(a0)});
        } else if (std::holds_alternative<typename uint::D1>(_sv.v())) {
          const auto &[a0] = std::get<typename uint::D1>(_sv.v());
          _stack.emplace_back(CraneCont_D1{});
          _stack.emplace_back(CraneEnter{crane_raw(a0)});
        } else if (std::holds_alternative<typename uint::D2>(_sv.v())) {
          const auto &[a0] = std::get<typename uint::D2>(_sv.v());
          _stack.emplace_back(CraneCont_D2{});
          _stack.emplace_back(CraneEnter{crane_raw(a0)});
        } else if (std::holds_alternative<typename uint::D3>(_sv.v())) {
          const auto &[a0] = std::get<typename uint::D3>(_sv.v());
          _stack.emplace_back(CraneCont_D3{});
          _stack.emplace_back(CraneEnter{crane_raw(a0)});
        } else if (std::holds_alternative<typename uint::D4>(_sv.v())) {
          const auto &[a0] = std::get<typename uint::D4>(_sv.v());
          _stack.emplace_back(CraneCont_D4{});
          _stack.emplace_back(CraneEnter{crane_raw(a0)});
        } else if (std::holds_alternative<typename uint::D5>(_sv.v())) {
          const auto &[a0] = std::get<typename uint::D5>(_sv.v());
          _stack.emplace_back(CraneCont_D5{});
          _stack.emplace_back(CraneEnter{crane_raw(a0)});
        } else if (std::holds_alternative<typename uint::D6>(_sv.v())) {
          const auto &[a0] = std::get<typename uint::D6>(_sv.v());
          _stack.emplace_back(CraneCont_D6{});
          _stack.emplace_back(CraneEnter{crane_raw(a0)});
        } else if (std::holds_alternative<typename uint::D7>(_sv.v())) {
          const auto &[a0] = std::get<typename uint::D7>(_sv.v());
          _stack.emplace_back(CraneCont_D7{});
          _stack.emplace_back(CraneEnter{crane_raw(a0)});
        } else if (std::holds_alternative<typename uint::D8>(_sv.v())) {
          const auto &[a0] = std::get<typename uint::D8>(_sv.v());
          _stack.emplace_back(CraneCont_D8{});
          _stack.emplace_back(CraneEnter{crane_raw(a0)});
        } else if (std::holds_alternative<typename uint::D9>(_sv.v())) {
          const auto &[a0] = std::get<typename uint::D9>(_sv.v());
          _stack.emplace_back(CraneCont_D9{});
          _stack.emplace_back(CraneEnter{crane_raw(a0)});
        } else if (std::holds_alternative<typename uint::Da>(_sv.v())) {
          const auto &[a0] = std::get<typename uint::Da>(_sv.v());
          _stack.emplace_back(CraneCont_Da{});
          _stack.emplace_back(CraneEnter{crane_raw(a0)});
        } else if (std::holds_alternative<typename uint::Db>(_sv.v())) {
          const auto &[a0] = std::get<typename uint::Db>(_sv.v());
          _stack.emplace_back(CraneCont_Db{});
          _stack.emplace_back(CraneEnter{crane_raw(a0)});
        } else if (std::holds_alternative<typename uint::Dc>(_sv.v())) {
          const auto &[a0] = std::get<typename uint::Dc>(_sv.v());
          _stack.emplace_back(CraneCont_Dc{});
          _stack.emplace_back(CraneEnter{crane_raw(a0)});
        } else if (std::holds_alternative<typename uint::Dd>(_sv.v())) {
          const auto &[a0] = std::get<typename uint::Dd>(_sv.v());
          _stack.emplace_back(CraneCont_Dd{});
          _stack.emplace_back(CraneEnter{crane_raw(a0)});
        } else if (std::holds_alternative<typename uint::De>(_sv.v())) {
          const auto &[a0] = std::get<typename uint::De>(_sv.v());
          _stack.emplace_back(CraneCont_De{});
          _stack.emplace_back(CraneEnter{crane_raw(a0)});
        } else {
          const auto &[a0] = std::get<typename uint::Df>(_sv.v());
          _stack.emplace_back(CraneCont_Df{});
          _stack.emplace_back(CraneEnter{crane_raw(a0)});
        }
      } else if (std::holds_alternative<CraneCont_D0>(_frame)) {
        auto _f = std::move(std::get<CraneCont_D0>(_frame));
        _result = (std::move(_result) + 1);
      } else if (std::holds_alternative<CraneCont_D1>(_frame)) {
        auto _f = std::move(std::get<CraneCont_D1>(_frame));
        _result = (std::move(_result) + 1);
      } else if (std::holds_alternative<CraneCont_D2>(_frame)) {
        auto _f = std::move(std::get<CraneCont_D2>(_frame));
        _result = (std::move(_result) + 1);
      } else if (std::holds_alternative<CraneCont_D3>(_frame)) {
        auto _f = std::move(std::get<CraneCont_D3>(_frame));
        _result = (std::move(_result) + 1);
      } else if (std::holds_alternative<CraneCont_D4>(_frame)) {
        auto _f = std::move(std::get<CraneCont_D4>(_frame));
        _result = (std::move(_result) + 1);
      } else if (std::holds_alternative<CraneCont_D5>(_frame)) {
        auto _f = std::move(std::get<CraneCont_D5>(_frame));
        _result = (std::move(_result) + 1);
      } else if (std::holds_alternative<CraneCont_D6>(_frame)) {
        auto _f = std::move(std::get<CraneCont_D6>(_frame));
        _result = (std::move(_result) + 1);
      } else if (std::holds_alternative<CraneCont_D7>(_frame)) {
        auto _f = std::move(std::get<CraneCont_D7>(_frame));
        _result = (std::move(_result) + 1);
      } else if (std::holds_alternative<CraneCont_D8>(_frame)) {
        auto _f = std::move(std::get<CraneCont_D8>(_frame));
        _result = (std::move(_result) + 1);
      } else if (std::holds_alternative<CraneCont_D9>(_frame)) {
        auto _f = std::move(std::get<CraneCont_D9>(_frame));
        _result = (std::move(_result) + 1);
      } else if (std::holds_alternative<CraneCont_Da>(_frame)) {
        auto _f = std::move(std::get<CraneCont_Da>(_frame));
        _result = (std::move(_result) + 1);
      } else if (std::holds_alternative<CraneCont_Db>(_frame)) {
        auto _f = std::move(std::get<CraneCont_Db>(_frame));
        _result = (std::move(_result) + 1);
      } else if (std::holds_alternative<CraneCont_Dc>(_frame)) {
        auto _f = std::move(std::get<CraneCont_Dc>(_frame));
        _result = (std::move(_result) + 1);
      } else if (std::holds_alternative<CraneCont_Dd>(_frame)) {
        auto _f = std::move(std::get<CraneCont_Dd>(_frame));
        _result = (std::move(_result) + 1);
      } else if (std::holds_alternative<CraneCont_De>(_frame)) {
        auto _f = std::move(std::get<CraneCont_De>(_frame));
        _result = (std::move(_result) + 1);
      } else {
        auto _f = std::move(std::get<CraneCont_Df>(_frame));
        _result = (std::move(_result) + 1);
      }
    }
    return _result;
  }

  uint nzhead() const {
    const uint *_loop_self = this;
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename uint::D0>(_sv.v())) {
        const auto &[a0] = std::get<typename uint::D0>(_sv.v());
        _loop_self = crane_raw(a0);
      } else {
        return *_loop_self;
      }
    }
  }

  uint unorm() const {
    auto &&_sv = this->nzhead();
    if (std::holds_alternative<typename uint::Nil>(_sv.v())) {
      return uint::d0(uint::nil());
    } else if (std::holds_alternative<typename uint::D0>(_sv.v())) {
      const auto &[a0] = std::get<typename uint::D0>(_sv.v());
      return uint::d0(*a0);
    } else if (std::holds_alternative<typename uint::D1>(_sv.v())) {
      const auto &[a0] = std::get<typename uint::D1>(_sv.v());
      return uint::d1(*a0);
    } else if (std::holds_alternative<typename uint::D2>(_sv.v())) {
      const auto &[a0] = std::get<typename uint::D2>(_sv.v());
      return uint::d2(*a0);
    } else if (std::holds_alternative<typename uint::D3>(_sv.v())) {
      const auto &[a0] = std::get<typename uint::D3>(_sv.v());
      return uint::d3(*a0);
    } else if (std::holds_alternative<typename uint::D4>(_sv.v())) {
      const auto &[a0] = std::get<typename uint::D4>(_sv.v());
      return uint::d4(*a0);
    } else if (std::holds_alternative<typename uint::D5>(_sv.v())) {
      const auto &[a0] = std::get<typename uint::D5>(_sv.v());
      return uint::d5(*a0);
    } else if (std::holds_alternative<typename uint::D6>(_sv.v())) {
      const auto &[a0] = std::get<typename uint::D6>(_sv.v());
      return uint::d6(*a0);
    } else if (std::holds_alternative<typename uint::D7>(_sv.v())) {
      const auto &[a0] = std::get<typename uint::D7>(_sv.v());
      return uint::d7(*a0);
    } else if (std::holds_alternative<typename uint::D8>(_sv.v())) {
      const auto &[a0] = std::get<typename uint::D8>(_sv.v());
      return uint::d8(*a0);
    } else if (std::holds_alternative<typename uint::D9>(_sv.v())) {
      const auto &[a0] = std::get<typename uint::D9>(_sv.v());
      return uint::d9(*a0);
    } else if (std::holds_alternative<typename uint::Da>(_sv.v())) {
      const auto &[a0] = std::get<typename uint::Da>(_sv.v());
      return uint::da(*a0);
    } else if (std::holds_alternative<typename uint::Db>(_sv.v())) {
      const auto &[a0] = std::get<typename uint::Db>(_sv.v());
      return uint::db(*a0);
    } else if (std::holds_alternative<typename uint::Dc>(_sv.v())) {
      const auto &[a0] = std::get<typename uint::Dc>(_sv.v());
      return uint::dc(*a0);
    } else if (std::holds_alternative<typename uint::Dd>(_sv.v())) {
      const auto &[a0] = std::get<typename uint::Dd>(_sv.v());
      return uint::dd(*a0);
    } else if (std::holds_alternative<typename uint::De>(_sv.v())) {
      const auto &[a0] = std::get<typename uint::De>(_sv.v());
      return uint::de(*a0);
    } else {
      const auto &[a0] = std::get<typename uint::Df>(_sv.v());
      return uint::df(*a0);
    }
  }

  uint revapp(uint d_) const {
    const uint *_loop_self = this;
    uint _loop_d_ = std::move(d_);
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename uint::Nil>(_sv.v())) {
        return _loop_d_;
      } else if (std::holds_alternative<typename uint::D0>(_sv.v())) {
        const auto &[a0] = std::get<typename uint::D0>(_sv.v());
        _loop_self = crane_raw(a0);
        _loop_d_ = uint::d0(std::move(_loop_d_));
      } else if (std::holds_alternative<typename uint::D1>(_sv.v())) {
        const auto &[a0] = std::get<typename uint::D1>(_sv.v());
        _loop_self = crane_raw(a0);
        _loop_d_ = uint::d1(std::move(_loop_d_));
      } else if (std::holds_alternative<typename uint::D2>(_sv.v())) {
        const auto &[a0] = std::get<typename uint::D2>(_sv.v());
        _loop_self = crane_raw(a0);
        _loop_d_ = uint::d2(std::move(_loop_d_));
      } else if (std::holds_alternative<typename uint::D3>(_sv.v())) {
        const auto &[a0] = std::get<typename uint::D3>(_sv.v());
        _loop_self = crane_raw(a0);
        _loop_d_ = uint::d3(std::move(_loop_d_));
      } else if (std::holds_alternative<typename uint::D4>(_sv.v())) {
        const auto &[a0] = std::get<typename uint::D4>(_sv.v());
        _loop_self = crane_raw(a0);
        _loop_d_ = uint::d4(std::move(_loop_d_));
      } else if (std::holds_alternative<typename uint::D5>(_sv.v())) {
        const auto &[a0] = std::get<typename uint::D5>(_sv.v());
        _loop_self = crane_raw(a0);
        _loop_d_ = uint::d5(std::move(_loop_d_));
      } else if (std::holds_alternative<typename uint::D6>(_sv.v())) {
        const auto &[a0] = std::get<typename uint::D6>(_sv.v());
        _loop_self = crane_raw(a0);
        _loop_d_ = uint::d6(std::move(_loop_d_));
      } else if (std::holds_alternative<typename uint::D7>(_sv.v())) {
        const auto &[a0] = std::get<typename uint::D7>(_sv.v());
        _loop_self = crane_raw(a0);
        _loop_d_ = uint::d7(std::move(_loop_d_));
      } else if (std::holds_alternative<typename uint::D8>(_sv.v())) {
        const auto &[a0] = std::get<typename uint::D8>(_sv.v());
        _loop_self = crane_raw(a0);
        _loop_d_ = uint::d8(std::move(_loop_d_));
      } else if (std::holds_alternative<typename uint::D9>(_sv.v())) {
        const auto &[a0] = std::get<typename uint::D9>(_sv.v());
        _loop_self = crane_raw(a0);
        _loop_d_ = uint::d9(std::move(_loop_d_));
      } else if (std::holds_alternative<typename uint::Da>(_sv.v())) {
        const auto &[a0] = std::get<typename uint::Da>(_sv.v());
        _loop_self = crane_raw(a0);
        _loop_d_ = uint::da(std::move(_loop_d_));
      } else if (std::holds_alternative<typename uint::Db>(_sv.v())) {
        const auto &[a0] = std::get<typename uint::Db>(_sv.v());
        _loop_self = crane_raw(a0);
        _loop_d_ = uint::db(std::move(_loop_d_));
      } else if (std::holds_alternative<typename uint::Dc>(_sv.v())) {
        const auto &[a0] = std::get<typename uint::Dc>(_sv.v());
        _loop_self = crane_raw(a0);
        _loop_d_ = uint::dc(std::move(_loop_d_));
      } else if (std::holds_alternative<typename uint::Dd>(_sv.v())) {
        const auto &[a0] = std::get<typename uint::Dd>(_sv.v());
        _loop_self = crane_raw(a0);
        _loop_d_ = uint::dd(std::move(_loop_d_));
      } else if (std::holds_alternative<typename uint::De>(_sv.v())) {
        const auto &[a0] = std::get<typename uint::De>(_sv.v());
        _loop_self = crane_raw(a0);
        _loop_d_ = uint::de(std::move(_loop_d_));
      } else {
        const auto &[a0] = std::get<typename uint::Df>(_sv.v());
        _loop_self = crane_raw(a0);
        _loop_d_ = uint::df(std::move(_loop_d_));
      }
    }
  }

  uint rev() const { return this->revapp(uint::nil()); }

  uint app(uint d_) const { return this->rev().revapp(std::move(d_)); }

  std::pair<uint, uint64_t> nztail() const {
    auto aux_impl = [](auto &_self_aux,
                       const uint &d_rev) -> std::pair<uint, uint64_t> {
      if (std::holds_alternative<typename uint::D0>(d_rev.v())) {
        const auto &[a0] = std::get<typename uint::D0>(d_rev.v());
        auto [r, n] = _self_aux(_self_aux, *a0);
        return std::make_pair(std::move(r), (n + 1));
      } else {
        return std::make_pair(d_rev, UINT64_C(0));
      }
    };
    auto aux = [&](const uint &d_rev) -> std::pair<uint, uint64_t> {
      return aux_impl(aux_impl, d_rev);
    };
    auto [r, n] = aux(this->rev());
    return std::make_pair(std::move(r).rev(), n);
  }

  uint del_head(uint64_t n) const {
    const uint *_loop_self = this;
    uint64_t _loop_n = n;
    while (true) {
      if (_loop_n <= 0) {
        return *_loop_self;
      } else {
        uint64_t n0 = _loop_n - 1;
        auto &&_sv = *_loop_self;
        if (std::holds_alternative<typename uint::Nil>(_sv.v())) {
          return uint::d0(uint::nil());
        } else if (std::holds_alternative<typename uint::D0>(_sv.v())) {
          const auto &[a0] = std::get<typename uint::D0>(_sv.v());
          _loop_self = crane_raw(a0);
          _loop_n = n0;
        } else if (std::holds_alternative<typename uint::D1>(_sv.v())) {
          const auto &[a0] = std::get<typename uint::D1>(_sv.v());
          _loop_self = crane_raw(a0);
          _loop_n = n0;
        } else if (std::holds_alternative<typename uint::D2>(_sv.v())) {
          const auto &[a0] = std::get<typename uint::D2>(_sv.v());
          _loop_self = crane_raw(a0);
          _loop_n = n0;
        } else if (std::holds_alternative<typename uint::D3>(_sv.v())) {
          const auto &[a0] = std::get<typename uint::D3>(_sv.v());
          _loop_self = crane_raw(a0);
          _loop_n = n0;
        } else if (std::holds_alternative<typename uint::D4>(_sv.v())) {
          const auto &[a0] = std::get<typename uint::D4>(_sv.v());
          _loop_self = crane_raw(a0);
          _loop_n = n0;
        } else if (std::holds_alternative<typename uint::D5>(_sv.v())) {
          const auto &[a0] = std::get<typename uint::D5>(_sv.v());
          _loop_self = crane_raw(a0);
          _loop_n = n0;
        } else if (std::holds_alternative<typename uint::D6>(_sv.v())) {
          const auto &[a0] = std::get<typename uint::D6>(_sv.v());
          _loop_self = crane_raw(a0);
          _loop_n = n0;
        } else if (std::holds_alternative<typename uint::D7>(_sv.v())) {
          const auto &[a0] = std::get<typename uint::D7>(_sv.v());
          _loop_self = crane_raw(a0);
          _loop_n = n0;
        } else if (std::holds_alternative<typename uint::D8>(_sv.v())) {
          const auto &[a0] = std::get<typename uint::D8>(_sv.v());
          _loop_self = crane_raw(a0);
          _loop_n = n0;
        } else if (std::holds_alternative<typename uint::D9>(_sv.v())) {
          const auto &[a0] = std::get<typename uint::D9>(_sv.v());
          _loop_self = crane_raw(a0);
          _loop_n = n0;
        } else if (std::holds_alternative<typename uint::Da>(_sv.v())) {
          const auto &[a0] = std::get<typename uint::Da>(_sv.v());
          _loop_self = crane_raw(a0);
          _loop_n = n0;
        } else if (std::holds_alternative<typename uint::Db>(_sv.v())) {
          const auto &[a0] = std::get<typename uint::Db>(_sv.v());
          _loop_self = crane_raw(a0);
          _loop_n = n0;
        } else if (std::holds_alternative<typename uint::Dc>(_sv.v())) {
          const auto &[a0] = std::get<typename uint::Dc>(_sv.v());
          _loop_self = crane_raw(a0);
          _loop_n = n0;
        } else if (std::holds_alternative<typename uint::Dd>(_sv.v())) {
          const auto &[a0] = std::get<typename uint::Dd>(_sv.v());
          _loop_self = crane_raw(a0);
          _loop_n = n0;
        } else if (std::holds_alternative<typename uint::De>(_sv.v())) {
          const auto &[a0] = std::get<typename uint::De>(_sv.v());
          _loop_self = crane_raw(a0);
          _loop_n = n0;
        } else {
          const auto &[a0] = std::get<typename uint::Df>(_sv.v());
          _loop_self = crane_raw(a0);
          _loop_n = n0;
        }
      }
    }
  }

  uint del_tail(uint64_t n) const { return this->rev().del_head(n).rev(); }
};

struct Signed_int {
  // TYPES
  struct Pos {
    uint d;
  };

  struct Neg {
    uint d;
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

  static signed_int pos(uint d) { return signed_int(Pos{std::move(d)}); }

  static signed_int neg(uint d) { return signed_int(Neg{std::move(d)}); }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  bool signed_int_beq(const signed_int &y) const {
    if (std::holds_alternative<typename signed_int::Pos>(this->v())) {
      const auto &[d0] = std::get<typename signed_int::Pos>(this->v());
      if (std::holds_alternative<typename signed_int::Pos>(y.v())) {
        const auto &[d2] = std::get<typename signed_int::Pos>(y.v());
        return d0.uint_beq(d2);
      } else {
        return false;
      }
    } else {
      const auto &[d0] = std::get<typename signed_int::Neg>(this->v());
      if (std::holds_alternative<typename signed_int::Pos>(y.v())) {
        return false;
      } else {
        const auto &[d2] = std::get<typename signed_int::Neg>(y.v());
        return d0.uint_beq(d2);
      }
    }
  }

  bool signed_int_eq_dec(const signed_int &y) const {
    bool h;
    bool b = this->signed_int_beq(y);
    if (b) {
      h = true;
    } else {
      h = false;
    }
    if (h) {
      return true;
    } else {
      return false;
    }
  }

  signed_int norm() const {
    if (std::holds_alternative<typename signed_int::Pos>(this->v())) {
      const auto &[d1] = std::get<typename signed_int::Pos>(this->v());
      return signed_int::pos(d1.unorm());
    } else {
      const auto &[d1] = std::get<typename signed_int::Neg>(this->v());
      auto &&_sv0 = d1.nzhead();
      if (std::holds_alternative<typename uint::Nil>(_sv0.v())) {
        return signed_int::pos(uint::d0(uint::nil()));
      } else if (std::holds_alternative<typename uint::D0>(_sv0.v())) {
        const auto &[a00] = std::get<typename uint::D0>(_sv0.v());
        return signed_int::neg(uint::d0(*a00));
      } else if (std::holds_alternative<typename uint::D1>(_sv0.v())) {
        const auto &[a00] = std::get<typename uint::D1>(_sv0.v());
        return signed_int::neg(uint::d1(*a00));
      } else if (std::holds_alternative<typename uint::D2>(_sv0.v())) {
        const auto &[a00] = std::get<typename uint::D2>(_sv0.v());
        return signed_int::neg(uint::d2(*a00));
      } else if (std::holds_alternative<typename uint::D3>(_sv0.v())) {
        const auto &[a00] = std::get<typename uint::D3>(_sv0.v());
        return signed_int::neg(uint::d3(*a00));
      } else if (std::holds_alternative<typename uint::D4>(_sv0.v())) {
        const auto &[a00] = std::get<typename uint::D4>(_sv0.v());
        return signed_int::neg(uint::d4(*a00));
      } else if (std::holds_alternative<typename uint::D5>(_sv0.v())) {
        const auto &[a00] = std::get<typename uint::D5>(_sv0.v());
        return signed_int::neg(uint::d5(*a00));
      } else if (std::holds_alternative<typename uint::D6>(_sv0.v())) {
        const auto &[a00] = std::get<typename uint::D6>(_sv0.v());
        return signed_int::neg(uint::d6(*a00));
      } else if (std::holds_alternative<typename uint::D7>(_sv0.v())) {
        const auto &[a00] = std::get<typename uint::D7>(_sv0.v());
        return signed_int::neg(uint::d7(*a00));
      } else if (std::holds_alternative<typename uint::D8>(_sv0.v())) {
        const auto &[a00] = std::get<typename uint::D8>(_sv0.v());
        return signed_int::neg(uint::d8(*a00));
      } else if (std::holds_alternative<typename uint::D9>(_sv0.v())) {
        const auto &[a00] = std::get<typename uint::D9>(_sv0.v());
        return signed_int::neg(uint::d9(*a00));
      } else if (std::holds_alternative<typename uint::Da>(_sv0.v())) {
        const auto &[a00] = std::get<typename uint::Da>(_sv0.v());
        return signed_int::neg(uint::da(*a00));
      } else if (std::holds_alternative<typename uint::Db>(_sv0.v())) {
        const auto &[a00] = std::get<typename uint::Db>(_sv0.v());
        return signed_int::neg(uint::db(*a00));
      } else if (std::holds_alternative<typename uint::Dc>(_sv0.v())) {
        const auto &[a00] = std::get<typename uint::Dc>(_sv0.v());
        return signed_int::neg(uint::dc(*a00));
      } else if (std::holds_alternative<typename uint::Dd>(_sv0.v())) {
        const auto &[a00] = std::get<typename uint::Dd>(_sv0.v());
        return signed_int::neg(uint::dd(*a00));
      } else if (std::holds_alternative<typename uint::De>(_sv0.v())) {
        const auto &[a00] = std::get<typename uint::De>(_sv0.v());
        return signed_int::neg(uint::de(*a00));
      } else {
        const auto &[a00] = std::get<typename uint::Df>(_sv0.v());
        return signed_int::neg(uint::df(*a00));
      }
    }
  }

  signed_int opp() const {
    if (std::holds_alternative<typename signed_int::Pos>(this->v())) {
      const auto &[d1] = std::get<typename signed_int::Pos>(this->v());
      return signed_int::neg(d1);
    } else {
      const auto &[d1] = std::get<typename signed_int::Neg>(this->v());
      return signed_int::pos(d1);
    }
  }

  uint abs() const {
    if (std::holds_alternative<typename signed_int::Pos>(this->v())) {
      const auto &[d1] = std::get<typename signed_int::Pos>(this->v());
      return d1;
    } else {
      const auto &[d1] = std::get<typename signed_int::Neg>(this->v());
      return d1;
    }
  }

  signed_int app_int(uint d2) const {
    if (std::holds_alternative<typename signed_int::Pos>(this->v())) {
      const auto &[d] = std::get<typename signed_int::Pos>(this->v());
      return signed_int::pos(d.app(std::move(d2)));
    } else {
      const auto &[d] = std::get<typename signed_int::Neg>(this->v());
      return signed_int::neg(d.app(std::move(d2)));
    }
  }

  std::pair<signed_int, uint64_t> nztail_int() const {
    if (std::holds_alternative<typename signed_int::Pos>(this->v())) {
      const auto &[d1] = std::get<typename signed_int::Pos>(this->v());
      auto [r, n] = d1.nztail();
      return std::make_pair(signed_int::pos(std::move(r)), n);
    } else {
      const auto &[d1] = std::get<typename signed_int::Neg>(this->v());
      auto [r, n] = d1.nztail();
      return std::make_pair(signed_int::neg(std::move(r)), n);
    }
  }

  uint del_head_int(uint64_t n) const {
    if (std::holds_alternative<typename signed_int::Pos>(this->v())) {
      const auto &[d1] = std::get<typename signed_int::Pos>(this->v());
      return d1.del_head(n);
    } else {
      const auto &[d1] = std::get<typename signed_int::Neg>(this->v());
      return d1.del_head(n);
    }
  }

  signed_int del_tail_int(uint64_t n) const {
    if (std::holds_alternative<typename signed_int::Pos>(this->v())) {
      const auto &[d1] = std::get<typename signed_int::Pos>(this->v());
      return signed_int::pos(d1.del_tail(n));
    } else {
      const auto &[d1] = std::get<typename signed_int::Neg>(this->v());
      return signed_int::neg(d1.del_tail(n));
    }
  }
};

struct Hexadecimal {
  // TYPES
  struct Hexadecimal0 {
    signed_int i;
    uint f;
  };

  struct HexadecimalExp {
    signed_int i;
    uint f;
    Decimal::signed_int e;
  };

  using variant_t = std::variant<Hexadecimal0, HexadecimalExp>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Hexadecimal() {}

  explicit Hexadecimal(Hexadecimal0 _v) : v_(std::move(_v)) {}

  explicit Hexadecimal(HexadecimalExp _v) : v_(std::move(_v)) {}

  static hexadecimal hexadecimal0(signed_int i, uint f) {
    return hexadecimal(Hexadecimal0{std::move(i), std::move(f)});
  }

  static hexadecimal hexadecimalexp(signed_int i, uint f,
                                    Decimal::signed_int e) {
    return hexadecimal(
        HexadecimalExp{std::move(i), std::move(f), std::move(e)});
  }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  bool hexadecimal_beq(const hexadecimal &y) const {
    if (std::holds_alternative<typename hexadecimal::Hexadecimal0>(this->v())) {
      const auto &[i0, f0] =
          std::get<typename hexadecimal::Hexadecimal0>(this->v());
      if (std::holds_alternative<typename hexadecimal::Hexadecimal0>(y.v())) {
        const auto &[i2, f2] =
            std::get<typename hexadecimal::Hexadecimal0>(y.v());
        return (i0.signed_int_beq(i2) && f0.uint_beq(f2));
      } else {
        return false;
      }
    } else {
      const auto &[i0, f0, e0] =
          std::get<typename hexadecimal::HexadecimalExp>(this->v());
      if (std::holds_alternative<typename hexadecimal::Hexadecimal0>(y.v())) {
        return false;
      } else {
        const auto &[i2, f2, e2] =
            std::get<typename hexadecimal::HexadecimalExp>(y.v());
        return (i0.signed_int_beq(i2) &&
                (f0.uint_beq(f2) && signed_int_beq(e0, e2)));
      }
    }
  }

  bool hexadecimal_eq_dec(const hexadecimal &y) const {
    bool h;
    bool b = this->hexadecimal_beq(y);
    if (b) {
      h = true;
    } else {
      h = false;
    }
    if (h) {
      return true;
    } else {
      return false;
    }
  }
};

#endif // INCLUDED_HEXADECIMAL
