#ifndef INCLUDED_DECIMAL
#define INCLUDED_DECIMAL

#include "crane_fn.h"
#include "small_vector.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <utility>
#include <variant>

namespace Decimal {

struct Uint;
struct Signed_int;
struct Decimal;

struct Little {
  static Uint succ(const Uint &d);
  static Uint double_(const Uint &d);
  static Uint succ_double(const Uint &d);
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

  template <typename T1, typename F1, typename F2, typename F3, typename F4,
            typename F5, typename F6, typename F7, typename F8, typename F9,
            typename F10>
  T1 uint_rect(T1 f, F1 &&f0, F2 &&f1, F3 &&f2, F4 &&f3, F5 &&f4, F6 &&f5,
               F7 &&f6, F8 &&f7, F9 &&f8, F10 &&f9) const {
    const Uint *_self = this;

    /// CraneEnter: captures varying parameters for each recursive call.
    struct CraneEnter {
      const Uint *_self;
    };

    /// CraneCont_D0: saves [a0], resumes after recursive call, then processes
    /// rest.
    struct CraneCont_D0 {
      std::shared_ptr<Uint> a0;
    };

    /// CraneCont_D1: saves [a0], resumes after recursive call, then processes
    /// rest.
    struct CraneCont_D1 {
      std::shared_ptr<Uint> a0;
    };

    /// CraneCont_D2: saves [a0], resumes after recursive call, then processes
    /// rest.
    struct CraneCont_D2 {
      std::shared_ptr<Uint> a0;
    };

    /// CraneCont_D3: saves [a0], resumes after recursive call, then processes
    /// rest.
    struct CraneCont_D3 {
      std::shared_ptr<Uint> a0;
    };

    /// CraneCont_D4: saves [a0], resumes after recursive call, then processes
    /// rest.
    struct CraneCont_D4 {
      std::shared_ptr<Uint> a0;
    };

    /// CraneCont_D5: saves [a0], resumes after recursive call, then processes
    /// rest.
    struct CraneCont_D5 {
      std::shared_ptr<Uint> a0;
    };

    /// CraneCont_D6: saves [a0], resumes after recursive call, then processes
    /// rest.
    struct CraneCont_D6 {
      std::shared_ptr<Uint> a0;
    };

    /// CraneCont_D7: saves [a0], resumes after recursive call, then processes
    /// rest.
    struct CraneCont_D7 {
      std::shared_ptr<Uint> a0;
    };

    /// CraneCont_D8: saves [a0], resumes after recursive call, then processes
    /// rest.
    struct CraneCont_D8 {
      std::shared_ptr<Uint> a0;
    };

    /// CraneCont_D9: saves [a0], resumes after recursive call, then processes
    /// rest.
    struct CraneCont_D9 {
      std::shared_ptr<Uint> a0;
    };

    using CraneFrame =
        std::variant<CraneEnter, CraneCont_D0, CraneCont_D1, CraneCont_D2,
                     CraneCont_D3, CraneCont_D4, CraneCont_D5, CraneCont_D6,
                     CraneCont_D7, CraneCont_D8, CraneCont_D9>;
    T1 _result{};
    crane::small_vector<CraneFrame> _stack;
    _stack.emplace_back(CraneEnter{_self});
    /// Loopified uint_rect: CraneEnter -> CraneCont_D0 -> CraneCont_D1 ->
    /// CraneCont_D2 -> CraneCont_D3 -> CraneCont_D4 -> CraneCont_D5 ->
    /// CraneCont_D6 -> CraneCont_D7 -> CraneCont_D8 -> CraneCont_D9.
    while (!_stack.empty()) {
      CraneFrame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<CraneEnter>(_frame)) {
        auto _f = std::move(std::get<CraneEnter>(_frame));
        const Uint *_self = _f._self;
        auto &&_sv = *_self;
        if (std::holds_alternative<typename Uint::Nil>(_sv.v())) {
          _result = f;
        } else if (std::holds_alternative<typename Uint::D0>(_sv.v())) {
          const auto &[a0] = std::get<typename Uint::D0>(_sv.v());
          _stack.emplace_back(CraneCont_D0{a0});
          _stack.emplace_back(CraneEnter{crane_raw(a0)});
        } else if (std::holds_alternative<typename Uint::D1>(_sv.v())) {
          const auto &[a0] = std::get<typename Uint::D1>(_sv.v());
          _stack.emplace_back(CraneCont_D1{a0});
          _stack.emplace_back(CraneEnter{crane_raw(a0)});
        } else if (std::holds_alternative<typename Uint::D2>(_sv.v())) {
          const auto &[a0] = std::get<typename Uint::D2>(_sv.v());
          _stack.emplace_back(CraneCont_D2{a0});
          _stack.emplace_back(CraneEnter{crane_raw(a0)});
        } else if (std::holds_alternative<typename Uint::D3>(_sv.v())) {
          const auto &[a0] = std::get<typename Uint::D3>(_sv.v());
          _stack.emplace_back(CraneCont_D3{a0});
          _stack.emplace_back(CraneEnter{crane_raw(a0)});
        } else if (std::holds_alternative<typename Uint::D4>(_sv.v())) {
          const auto &[a0] = std::get<typename Uint::D4>(_sv.v());
          _stack.emplace_back(CraneCont_D4{a0});
          _stack.emplace_back(CraneEnter{crane_raw(a0)});
        } else if (std::holds_alternative<typename Uint::D5>(_sv.v())) {
          const auto &[a0] = std::get<typename Uint::D5>(_sv.v());
          _stack.emplace_back(CraneCont_D5{a0});
          _stack.emplace_back(CraneEnter{crane_raw(a0)});
        } else if (std::holds_alternative<typename Uint::D6>(_sv.v())) {
          const auto &[a0] = std::get<typename Uint::D6>(_sv.v());
          _stack.emplace_back(CraneCont_D6{a0});
          _stack.emplace_back(CraneEnter{crane_raw(a0)});
        } else if (std::holds_alternative<typename Uint::D7>(_sv.v())) {
          const auto &[a0] = std::get<typename Uint::D7>(_sv.v());
          _stack.emplace_back(CraneCont_D7{a0});
          _stack.emplace_back(CraneEnter{crane_raw(a0)});
        } else if (std::holds_alternative<typename Uint::D8>(_sv.v())) {
          const auto &[a0] = std::get<typename Uint::D8>(_sv.v());
          _stack.emplace_back(CraneCont_D8{a0});
          _stack.emplace_back(CraneEnter{crane_raw(a0)});
        } else {
          const auto &[a0] = std::get<typename Uint::D9>(_sv.v());
          _stack.emplace_back(CraneCont_D9{a0});
          _stack.emplace_back(CraneEnter{crane_raw(a0)});
        }
      } else if (std::holds_alternative<CraneCont_D0>(_frame)) {
        auto _f = std::move(std::get<CraneCont_D0>(_frame));
        std::shared_ptr<Uint> a0 = std::move(_f.a0);
        _result = f0(*a0, std::move(_result));
      } else if (std::holds_alternative<CraneCont_D1>(_frame)) {
        auto _f = std::move(std::get<CraneCont_D1>(_frame));
        std::shared_ptr<Uint> a0 = std::move(_f.a0);
        _result = f1(*a0, std::move(_result));
      } else if (std::holds_alternative<CraneCont_D2>(_frame)) {
        auto _f = std::move(std::get<CraneCont_D2>(_frame));
        std::shared_ptr<Uint> a0 = std::move(_f.a0);
        _result = f2(*a0, std::move(_result));
      } else if (std::holds_alternative<CraneCont_D3>(_frame)) {
        auto _f = std::move(std::get<CraneCont_D3>(_frame));
        std::shared_ptr<Uint> a0 = std::move(_f.a0);
        _result = f3(*a0, std::move(_result));
      } else if (std::holds_alternative<CraneCont_D4>(_frame)) {
        auto _f = std::move(std::get<CraneCont_D4>(_frame));
        std::shared_ptr<Uint> a0 = std::move(_f.a0);
        _result = f4(*a0, std::move(_result));
      } else if (std::holds_alternative<CraneCont_D5>(_frame)) {
        auto _f = std::move(std::get<CraneCont_D5>(_frame));
        std::shared_ptr<Uint> a0 = std::move(_f.a0);
        _result = f5(*a0, std::move(_result));
      } else if (std::holds_alternative<CraneCont_D6>(_frame)) {
        auto _f = std::move(std::get<CraneCont_D6>(_frame));
        std::shared_ptr<Uint> a0 = std::move(_f.a0);
        _result = f6(*a0, std::move(_result));
      } else if (std::holds_alternative<CraneCont_D7>(_frame)) {
        auto _f = std::move(std::get<CraneCont_D7>(_frame));
        std::shared_ptr<Uint> a0 = std::move(_f.a0);
        _result = f7(*a0, std::move(_result));
      } else if (std::holds_alternative<CraneCont_D8>(_frame)) {
        auto _f = std::move(std::get<CraneCont_D8>(_frame));
        std::shared_ptr<Uint> a0 = std::move(_f.a0);
        _result = f8(*a0, std::move(_result));
      } else {
        auto _f = std::move(std::get<CraneCont_D9>(_frame));
        std::shared_ptr<Uint> a0 = std::move(_f.a0);
        _result = f9(*a0, std::move(_result));
      }
    }
    return _result;
  }

  template <typename T1, typename F1, typename F2, typename F3, typename F4,
            typename F5, typename F6, typename F7, typename F8, typename F9,
            typename F10>
  T1 uint_rec(T1 f, F1 &&f0, F2 &&f1, F3 &&f2, F4 &&f3, F5 &&f4, F6 &&f5,
              F7 &&f6, F8 &&f7, F9 &&f8, F10 &&f9) const {
    return this->template uint_rect<T1>(std::move(f), f0, f1, f2, f3, f4, f5,
                                        f6, f7, f8, f9);
  }

  bool uint_beq(const Uint &y) const {
    const Uint *_loop_self = this;
    const Uint *_loop_y = &y;
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename Uint::Nil>(_sv.v())) {
        if (std::holds_alternative<typename Uint::Nil>(_loop_y->v())) {
          return true;
        } else {
          return false;
        }
      } else if (std::holds_alternative<typename Uint::D0>(_sv.v())) {
        const auto &[a0] = std::get<typename Uint::D0>(_sv.v());
        if (std::holds_alternative<typename Uint::D0>(_loop_y->v())) {
          const auto &[a00] = std::get<typename Uint::D0>(_loop_y->v());
          _loop_self = crane_raw(a0);
          _loop_y = crane_raw(a00);
        } else {
          return false;
        }
      } else if (std::holds_alternative<typename Uint::D1>(_sv.v())) {
        const auto &[a0] = std::get<typename Uint::D1>(_sv.v());
        if (std::holds_alternative<typename Uint::D1>(_loop_y->v())) {
          const auto &[a00] = std::get<typename Uint::D1>(_loop_y->v());
          _loop_self = crane_raw(a0);
          _loop_y = crane_raw(a00);
        } else {
          return false;
        }
      } else if (std::holds_alternative<typename Uint::D2>(_sv.v())) {
        const auto &[a0] = std::get<typename Uint::D2>(_sv.v());
        if (std::holds_alternative<typename Uint::D2>(_loop_y->v())) {
          const auto &[a00] = std::get<typename Uint::D2>(_loop_y->v());
          _loop_self = crane_raw(a0);
          _loop_y = crane_raw(a00);
        } else {
          return false;
        }
      } else if (std::holds_alternative<typename Uint::D3>(_sv.v())) {
        const auto &[a0] = std::get<typename Uint::D3>(_sv.v());
        if (std::holds_alternative<typename Uint::D3>(_loop_y->v())) {
          const auto &[a00] = std::get<typename Uint::D3>(_loop_y->v());
          _loop_self = crane_raw(a0);
          _loop_y = crane_raw(a00);
        } else {
          return false;
        }
      } else if (std::holds_alternative<typename Uint::D4>(_sv.v())) {
        const auto &[a0] = std::get<typename Uint::D4>(_sv.v());
        if (std::holds_alternative<typename Uint::D4>(_loop_y->v())) {
          const auto &[a00] = std::get<typename Uint::D4>(_loop_y->v());
          _loop_self = crane_raw(a0);
          _loop_y = crane_raw(a00);
        } else {
          return false;
        }
      } else if (std::holds_alternative<typename Uint::D5>(_sv.v())) {
        const auto &[a0] = std::get<typename Uint::D5>(_sv.v());
        if (std::holds_alternative<typename Uint::D5>(_loop_y->v())) {
          const auto &[a00] = std::get<typename Uint::D5>(_loop_y->v());
          _loop_self = crane_raw(a0);
          _loop_y = crane_raw(a00);
        } else {
          return false;
        }
      } else if (std::holds_alternative<typename Uint::D6>(_sv.v())) {
        const auto &[a0] = std::get<typename Uint::D6>(_sv.v());
        if (std::holds_alternative<typename Uint::D6>(_loop_y->v())) {
          const auto &[a00] = std::get<typename Uint::D6>(_loop_y->v());
          _loop_self = crane_raw(a0);
          _loop_y = crane_raw(a00);
        } else {
          return false;
        }
      } else if (std::holds_alternative<typename Uint::D7>(_sv.v())) {
        const auto &[a0] = std::get<typename Uint::D7>(_sv.v());
        if (std::holds_alternative<typename Uint::D7>(_loop_y->v())) {
          const auto &[a00] = std::get<typename Uint::D7>(_loop_y->v());
          _loop_self = crane_raw(a0);
          _loop_y = crane_raw(a00);
        } else {
          return false;
        }
      } else if (std::holds_alternative<typename Uint::D8>(_sv.v())) {
        const auto &[a0] = std::get<typename Uint::D8>(_sv.v());
        if (std::holds_alternative<typename Uint::D8>(_loop_y->v())) {
          const auto &[a00] = std::get<typename Uint::D8>(_loop_y->v());
          _loop_self = crane_raw(a0);
          _loop_y = crane_raw(a00);
        } else {
          return false;
        }
      } else {
        const auto &[a0] = std::get<typename Uint::D9>(_sv.v());
        if (std::holds_alternative<typename Uint::D9>(_loop_y->v())) {
          const auto &[a00] = std::get<typename Uint::D9>(_loop_y->v());
          _loop_self = crane_raw(a0);
          _loop_y = crane_raw(a00);
        } else {
          return false;
        }
      }
    }
  }

  bool uint_eq_dec(const Uint &y) const {
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
    const Uint *_self = this;

    /// CraneEnter: captures varying parameters for each recursive call.
    struct CraneEnter {
      const Uint *_self;
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

    using CraneFrame =
        std::variant<CraneEnter, CraneCont_D0, CraneCont_D1, CraneCont_D2,
                     CraneCont_D3, CraneCont_D4, CraneCont_D5, CraneCont_D6,
                     CraneCont_D7, CraneCont_D8, CraneCont_D9>;
    uint64_t _result{};
    crane::small_vector<CraneFrame> _stack;
    _stack.emplace_back(CraneEnter{_self});
    /// Loopified nb_digits: CraneEnter -> CraneCont_D0 -> CraneCont_D1 ->
    /// CraneCont_D2 -> CraneCont_D3 -> CraneCont_D4 -> CraneCont_D5 ->
    /// CraneCont_D6 -> CraneCont_D7 -> CraneCont_D8 -> CraneCont_D9.
    while (!_stack.empty()) {
      CraneFrame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<CraneEnter>(_frame)) {
        auto _f = std::move(std::get<CraneEnter>(_frame));
        const Uint *_self = _f._self;
        auto &&_sv = *_self;
        if (std::holds_alternative<typename Uint::Nil>(_sv.v())) {
          _result = UINT64_C(0);
        } else if (std::holds_alternative<typename Uint::D0>(_sv.v())) {
          const auto &[a0] = std::get<typename Uint::D0>(_sv.v());
          _stack.emplace_back(CraneCont_D0{});
          _stack.emplace_back(CraneEnter{crane_raw(a0)});
        } else if (std::holds_alternative<typename Uint::D1>(_sv.v())) {
          const auto &[a0] = std::get<typename Uint::D1>(_sv.v());
          _stack.emplace_back(CraneCont_D1{});
          _stack.emplace_back(CraneEnter{crane_raw(a0)});
        } else if (std::holds_alternative<typename Uint::D2>(_sv.v())) {
          const auto &[a0] = std::get<typename Uint::D2>(_sv.v());
          _stack.emplace_back(CraneCont_D2{});
          _stack.emplace_back(CraneEnter{crane_raw(a0)});
        } else if (std::holds_alternative<typename Uint::D3>(_sv.v())) {
          const auto &[a0] = std::get<typename Uint::D3>(_sv.v());
          _stack.emplace_back(CraneCont_D3{});
          _stack.emplace_back(CraneEnter{crane_raw(a0)});
        } else if (std::holds_alternative<typename Uint::D4>(_sv.v())) {
          const auto &[a0] = std::get<typename Uint::D4>(_sv.v());
          _stack.emplace_back(CraneCont_D4{});
          _stack.emplace_back(CraneEnter{crane_raw(a0)});
        } else if (std::holds_alternative<typename Uint::D5>(_sv.v())) {
          const auto &[a0] = std::get<typename Uint::D5>(_sv.v());
          _stack.emplace_back(CraneCont_D5{});
          _stack.emplace_back(CraneEnter{crane_raw(a0)});
        } else if (std::holds_alternative<typename Uint::D6>(_sv.v())) {
          const auto &[a0] = std::get<typename Uint::D6>(_sv.v());
          _stack.emplace_back(CraneCont_D6{});
          _stack.emplace_back(CraneEnter{crane_raw(a0)});
        } else if (std::holds_alternative<typename Uint::D7>(_sv.v())) {
          const auto &[a0] = std::get<typename Uint::D7>(_sv.v());
          _stack.emplace_back(CraneCont_D7{});
          _stack.emplace_back(CraneEnter{crane_raw(a0)});
        } else if (std::holds_alternative<typename Uint::D8>(_sv.v())) {
          const auto &[a0] = std::get<typename Uint::D8>(_sv.v());
          _stack.emplace_back(CraneCont_D8{});
          _stack.emplace_back(CraneEnter{crane_raw(a0)});
        } else {
          const auto &[a0] = std::get<typename Uint::D9>(_sv.v());
          _stack.emplace_back(CraneCont_D9{});
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
      } else {
        auto _f = std::move(std::get<CraneCont_D9>(_frame));
        _result = (std::move(_result) + 1);
      }
    }
    return _result;
  }

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

  Uint app(Uint d_) const { return this->rev().revapp(std::move(d_)); }

  std::pair<Uint, uint64_t> nztail() const {
    auto aux_impl = [](auto &_self_aux,
                       const Uint &d_rev) -> std::pair<Uint, uint64_t> {
      if (std::holds_alternative<typename Uint::D0>(d_rev.v())) {
        const auto &[a0] = std::get<typename Uint::D0>(d_rev.v());
        auto [r, n] = _self_aux(_self_aux, *a0);
        return std::make_pair(std::move(r), (n + 1));
      } else {
        return std::make_pair(d_rev, UINT64_C(0));
      }
    };
    auto aux = [&](const Uint &d_rev) -> std::pair<Uint, uint64_t> {
      return aux_impl(aux_impl, d_rev);
    };
    auto [r, n] = aux(this->rev());
    return std::make_pair(r.rev(), n);
  }

  Uint del_head(uint64_t n) const {
    const Uint *_loop_self = this;
    uint64_t _loop_n = n;
    while (true) {
      if (_loop_n <= 0) {
        return *_loop_self;
      } else {
        uint64_t n0 = _loop_n - 1;
        auto &&_sv = *_loop_self;
        if (std::holds_alternative<typename Uint::Nil>(_sv.v())) {
          return Uint::d0(Uint::nil());
        } else if (std::holds_alternative<typename Uint::D0>(_sv.v())) {
          const auto &[a0] = std::get<typename Uint::D0>(_sv.v());
          _loop_self = crane_raw(a0);
          _loop_n = n0;
        } else if (std::holds_alternative<typename Uint::D1>(_sv.v())) {
          const auto &[a0] = std::get<typename Uint::D1>(_sv.v());
          _loop_self = crane_raw(a0);
          _loop_n = n0;
        } else if (std::holds_alternative<typename Uint::D2>(_sv.v())) {
          const auto &[a0] = std::get<typename Uint::D2>(_sv.v());
          _loop_self = crane_raw(a0);
          _loop_n = n0;
        } else if (std::holds_alternative<typename Uint::D3>(_sv.v())) {
          const auto &[a0] = std::get<typename Uint::D3>(_sv.v());
          _loop_self = crane_raw(a0);
          _loop_n = n0;
        } else if (std::holds_alternative<typename Uint::D4>(_sv.v())) {
          const auto &[a0] = std::get<typename Uint::D4>(_sv.v());
          _loop_self = crane_raw(a0);
          _loop_n = n0;
        } else if (std::holds_alternative<typename Uint::D5>(_sv.v())) {
          const auto &[a0] = std::get<typename Uint::D5>(_sv.v());
          _loop_self = crane_raw(a0);
          _loop_n = n0;
        } else if (std::holds_alternative<typename Uint::D6>(_sv.v())) {
          const auto &[a0] = std::get<typename Uint::D6>(_sv.v());
          _loop_self = crane_raw(a0);
          _loop_n = n0;
        } else if (std::holds_alternative<typename Uint::D7>(_sv.v())) {
          const auto &[a0] = std::get<typename Uint::D7>(_sv.v());
          _loop_self = crane_raw(a0);
          _loop_n = n0;
        } else if (std::holds_alternative<typename Uint::D8>(_sv.v())) {
          const auto &[a0] = std::get<typename Uint::D8>(_sv.v());
          _loop_self = crane_raw(a0);
          _loop_n = n0;
        } else {
          const auto &[a0] = std::get<typename Uint::D9>(_sv.v());
          _loop_self = crane_raw(a0);
          _loop_n = n0;
        }
      }
    }
  }

  Uint del_tail(uint64_t n) const { return this->rev().del_head(n).rev(); }

  Uint uint_of_uint() const { return std::move(*this); }
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

  bool signed_int_beq(const Signed_int &y) const {
    if (std::holds_alternative<typename Signed_int::Pos>(this->v())) {
      const auto &[d0] = std::get<typename Signed_int::Pos>(this->v());
      if (std::holds_alternative<typename Signed_int::Pos>(y.v())) {
        const auto &[d2] = std::get<typename Signed_int::Pos>(y.v());
        return d0.uint_beq(d2);
      } else {
        return false;
      }
    } else {
      const auto &[d0] = std::get<typename Signed_int::Neg>(this->v());
      if (std::holds_alternative<typename Signed_int::Pos>(y.v())) {
        return false;
      } else {
        const auto &[d2] = std::get<typename Signed_int::Neg>(y.v());
        return d0.uint_beq(d2);
      }
    }
  }

  bool signed_int_eq_dec(const Signed_int &y) const {
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

  Signed_int opp() const {
    if (std::holds_alternative<typename Signed_int::Pos>(this->v())) {
      const auto &[d1] = std::get<typename Signed_int::Pos>(this->v());
      return Signed_int::neg(d1);
    } else {
      const auto &[d1] = std::get<typename Signed_int::Neg>(this->v());
      return Signed_int::pos(d1);
    }
  }

  Uint abs() const {
    if (std::holds_alternative<typename Signed_int::Pos>(this->v())) {
      const auto &[d1] = std::get<typename Signed_int::Pos>(this->v());
      return d1;
    } else {
      const auto &[d1] = std::get<typename Signed_int::Neg>(this->v());
      return d1;
    }
  }

  Signed_int app_int(Uint d2) const {
    if (std::holds_alternative<typename Signed_int::Pos>(this->v())) {
      const auto &[d] = std::get<typename Signed_int::Pos>(this->v());
      return Signed_int::pos(d.app(std::move(d2)));
    } else {
      const auto &[d] = std::get<typename Signed_int::Neg>(this->v());
      return Signed_int::neg(d.app(std::move(d2)));
    }
  }

  std::pair<Signed_int, uint64_t> nztail_int() const {
    if (std::holds_alternative<typename Signed_int::Pos>(this->v())) {
      const auto &[d1] = std::get<typename Signed_int::Pos>(this->v());
      auto [r, n] = d1.nztail();
      return std::make_pair(Signed_int::pos(std::move(r)), n);
    } else {
      const auto &[d1] = std::get<typename Signed_int::Neg>(this->v());
      auto [r, n] = d1.nztail();
      return std::make_pair(Signed_int::neg(std::move(r)), n);
    }
  }

  Uint del_head_int(uint64_t n) const {
    if (std::holds_alternative<typename Signed_int::Pos>(this->v())) {
      const auto &[d1] = std::get<typename Signed_int::Pos>(this->v());
      return d1.del_head(n);
    } else {
      const auto &[d1] = std::get<typename Signed_int::Neg>(this->v());
      return d1.del_head(n);
    }
  }

  Signed_int del_tail_int(uint64_t n) const {
    if (std::holds_alternative<typename Signed_int::Pos>(this->v())) {
      const auto &[d1] = std::get<typename Signed_int::Pos>(this->v());
      return Signed_int::pos(d1.del_tail(n));
    } else {
      const auto &[d1] = std::get<typename Signed_int::Neg>(this->v());
      return Signed_int::neg(d1.del_tail(n));
    }
  }

  Signed_int int_of_int() const { return std::move(*this); }
};

struct Decimal {
  // TYPES
  struct Decimal0 {
    Signed_int i;
    Uint f;
  };

  struct DecimalExp {
    Signed_int i;
    Uint f;
    Signed_int e;
  };

  using variant_t = std::variant<Decimal0, DecimalExp>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Decimal() {}

  explicit Decimal(Decimal0 _v) : v_(std::move(_v)) {}

  explicit Decimal(DecimalExp _v) : v_(std::move(_v)) {}

  static Decimal decimal0(Signed_int i, Uint f) {
    return Decimal(Decimal0{std::move(i), std::move(f)});
  }

  static Decimal decimalexp(Signed_int i, Uint f, Signed_int e) {
    return Decimal(DecimalExp{std::move(i), std::move(f), std::move(e)});
  }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  bool decimal_beq(const Decimal &y) const {
    if (std::holds_alternative<typename Decimal::Decimal0>(this->v())) {
      const auto &[i0, f0] = std::get<typename Decimal::Decimal0>(this->v());
      if (std::holds_alternative<typename Decimal::Decimal0>(y.v())) {
        const auto &[i2, f2] = std::get<typename Decimal::Decimal0>(y.v());
        return (i0.signed_int_beq(i2) && f0.uint_beq(f2));
      } else {
        return false;
      }
    } else {
      const auto &[i0, f0, e0] =
          std::get<typename Decimal::DecimalExp>(this->v());
      if (std::holds_alternative<typename Decimal::Decimal0>(y.v())) {
        return false;
      } else {
        const auto &[i2, f2, e2] =
            std::get<typename Decimal::DecimalExp>(y.v());
        return (i0.signed_int_beq(i2) &&
                (f0.uint_beq(f2) && e0.signed_int_beq(e2)));
      }
    }
  }

  bool decimal_eq_dec(const Decimal &y) const {
    bool h;
    bool b = this->decimal_beq(y);
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

} // namespace Decimal

#endif // INCLUDED_DECIMAL
