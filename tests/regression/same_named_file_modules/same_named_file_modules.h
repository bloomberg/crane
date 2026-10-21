#ifndef INCLUDED_SAME_NAMED_FILE_MODULES
#define INCLUDED_SAME_NAMED_FILE_MODULES

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include "small_vector.h"
#include <atomic>
#include <concepts>
#include <cstdint>
#include <memory>
#include <optional>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

enum class Reflect;
template <typename A> struct List;
enum class Comparison;
enum class CompareSpecT;
struct Uint;
struct Signed_int;
struct Uint0;
struct Signed_int0;
struct Positive;
struct N;
struct Uint1;
struct Signed_int1;
template <typename X> struct Compare;

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

  template <typename CraneU>
  List(const List<CraneU> &_other)
      : v_([&]() -> variant_t {
          if (std::holds_alternative<typename List<CraneU>::Nil>(_other.v())) {
            return Nil{};
          } else {
            const auto &[a, l] =
                std::get<typename List<CraneU>::Cons>(_other.v());
            return Cons{
                [&]() -> A {
                  if constexpr (crane_convertible<A, const CraneU &>) {
                    return crane_convert<A>(a);
                  } else {
                    throw std::logic_error("unreachable: inactive constructor "
                                           "field at this instantiation");
                  }
                }(),
                (l ? std::make_shared<List<A>>(crane_convert<List<A>>(*l))
                   : nullptr)};
          }
        }()) {}

  static List<A> nil() { return List<A>(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List<A>(Cons{std::move(a), std::make_shared<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  ~List() {
    auto _next = [&](variant_t &_v) -> std::shared_ptr<List<A>> {
      if (auto *_alt = std::get_if<Cons>(&_v)) {
        if (_alt->l && _alt->l.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          return std::move(_alt->l);
        }
      }
      return nullptr;
    };
    std::shared_ptr<List<A>> _cur = _next(v_mut());
    while (_cur) {
      _cur = _next(_cur->v_mut());
    }
  }

  List(const List &) = default;
  List &operator=(const List &) = default;
  List(List &&) = default;
  List &operator=(List &&) = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, A &, T1 &&>
  T1 fold_right(F0 &&f, T1 a0) const {
    const List<A> *_self = this;

    /// CraneEnter: captures varying parameters for each recursive call.
    struct CraneEnter {
      const List<A> *_self;
    };

    /// CraneCont_Cons: saves [a1], resumes after recursive call, then processes
    /// rest.
    struct CraneCont_Cons {
      A a1;
    };

    using CraneFrame = std::variant<CraneEnter, CraneCont_Cons>;
    T1 _result{};
    crane::small_vector<CraneFrame> _stack;
    _stack.emplace_back(CraneEnter{_self});
    /// Loopified fold_right: CraneEnter -> CraneCont_Cons.
    while (!_stack.empty()) {
      CraneFrame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<CraneEnter>(_frame)) {
        auto _f = std::move(std::get<CraneEnter>(_frame));
        const List<A> *_self = _f._self;
        auto &&_sv = *_self;
        if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
          _result = a0;
        } else {
          const auto &[a1, a2] = std::get<typename List<A>::Cons>(_sv.v());
          _stack.emplace_back(CraneCont_Cons{a1});
          _stack.emplace_back(CraneEnter{crane_raw(a2)});
        }
      } else {
        auto _f = std::move(std::get<CraneCont_Cons>(_frame));
        auto a1 = std::move(_f.a1);
        _result = f(a1, std::move(_result));
      }
    }
    return _result;
  }

  uint64_t length() const {
    const List<A> *_self = this;

    /// CraneEnter: captures varying parameters for each recursive call.
    struct CraneEnter {
      const List<A> *_self;
    };

    /// CraneCont_Cons: resumes after recursive call, then processes rest.
    struct CraneCont_Cons {};

    using CraneFrame = std::variant<CraneEnter, CraneCont_Cons>;
    uint64_t _result{};
    crane::small_vector<CraneFrame> _stack;
    _stack.emplace_back(CraneEnter{_self});
    /// Loopified length: CraneEnter -> CraneCont_Cons.
    while (!_stack.empty()) {
      CraneFrame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<CraneEnter>(_frame)) {
        auto _f = std::move(std::get<CraneEnter>(_frame));
        const List<A> *_self = _f._self;
        auto &&_sv = *_self;
        if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
          _result = UINT64_C(0);
        } else {
          const auto &[a0, a1] = std::get<typename List<A>::Cons>(_sv.v());
          _stack.emplace_back(CraneCont_Cons{});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        }
      } else {
        auto _f = std::move(std::get<CraneCont_Cons>(_frame));
        _result = (std::move(_result) + 1);
      }
    }
    return _result;
  }
};
enum class Comparison { EQ, LT, GT };
enum class CompareSpecT { COMPEQT, COMPLTT, COMPGTT };
template <typename a = void> using CompSpecT = CompareSpecT;

struct Datatypes {
  static CompareSpecT CompareSpec2Type(Comparison c);
  template <typename T1>
  static CompSpecT<T1> CompSpec2Type(const T1 &_x, const T1 &_x0,
                                     Comparison x0_);
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
};

template <typename M>
concept EqLtLe = requires { typename M::t; };

struct Positive {
  // TYPES
  struct XI {
    std::shared_ptr<Positive> a0;
  };

  struct XO {
    std::shared_ptr<Positive> a0;
  };

  struct XH {};

  using variant_t = std::variant<XI, XO, XH>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Positive() {}

  explicit Positive(XI _v) : v_(std::move(_v)) {}

  explicit Positive(XO _v) : v_(std::move(_v)) {}

  explicit Positive(XH _v) : v_(_v) {}

  static Positive xi(Positive a0) {
    return Positive(XI{std::make_shared<Positive>(std::move(a0))});
  }

  static Positive xo(Positive a0) {
    return Positive(XO{std::make_shared<Positive>(std::move(a0))});
  }

  static Positive xh() { return Positive(XH{}); }

  // MANIPULATORS
  ~Positive() {
    auto _next = [&](variant_t &_v) -> std::shared_ptr<Positive> {
      if (auto *_alt = std::get_if<XI>(&_v)) {
        if (_alt->a0 && _alt->a0.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          return std::move(_alt->a0);
        }
      }
      if (auto *_alt = std::get_if<XO>(&_v)) {
        if (_alt->a0 && _alt->a0.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          return std::move(_alt->a0);
        }
      }
      return nullptr;
    };
    std::shared_ptr<Positive> _cur = _next(v_mut());
    while (_cur) {
      _cur = _next(_cur->v_mut());
    }
  }

  Positive(const Positive &) = default;
  Positive &operator=(const Positive &) = default;
  Positive(Positive &&) = default;
  Positive &operator=(Positive &&) = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct N {
  // TYPES
  struct N0 {};

  struct Npos {
    Positive a0;
  };

  using variant_t = std::variant<N0, Npos>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  N() {}

  explicit N(N0 _v) : v_(_v) {}

  explicit N(Npos _v) : v_(std::move(_v)) {}

  static N n0() { return N(N0{}); }

  static N npos(Positive a0) { return N(Npos{std::move(a0)}); }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
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

template <EqLtLe O, typename P> struct MakeOrderTac {};

struct Pos {
  struct mask {
    // TYPES
    struct IsNul {};

    struct IsPos {
      Positive a0;
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

    static mask ispos(Positive a0) { return mask(IsPos{std::move(a0)}); }

    static mask isneg() { return mask(IsNeg{}); }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };
};

template <typename X> struct Compare {
  // TYPES
  struct LT {};

  struct EQ {};

  struct GT {};

  using variant_t = std::variant<LT, EQ, GT>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Compare() {}

  explicit Compare(LT _v) : v_(_v) {}

  explicit Compare(EQ _v) : v_(_v) {}

  explicit Compare(GT _v) : v_(_v) {}

  static Compare<X> lt() { return Compare<X>(LT{}); }

  static Compare<X> eq() { return Compare<X>(EQ{}); }

  static Compare<X> gt() { return Compare<X>(GT{}); }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

template <typename M>
concept OrderedType = requires {
  typename M::t;
  {
    M::compare(std::declval<typename M::t>(), std::declval<typename M::t>())
  } -> std::same_as<Compare<typename M::t>>;
  {
    M::eq_dec(std::declval<typename M::t>(), std::declval<typename M::t>())
  } -> std::same_as<bool>;
};

template <OrderedType O> struct OrderedTypeFacts {
  struct TO {
    using t = typename O::t;
  };

  struct IsTO {};

  using OrderTac = MakeOrderTac<TO, IsTO>;

  static bool eq_dec(typename O::t x0_, typename O::t x1_) {
    return O::eq_dec(std::move(x0_), std::move(x1_));
  }

  static bool lt_dec(typename O::t x, typename O::t y) {
    auto &&_sv = O::compare(x, y);
    if (std::holds_alternative<typename Compare<typename O::t>::LT>(_sv.v())) {
      return true;
    } else {
      return false;
    }
  }

  static bool eqb(typename O::t x, typename O::t y) {
    if (eq_dec(std::move(x), std::move(y))) {
      return true;
    } else {
      return false;
    }
  }
};

template <OrderedType O> struct KeyOrderedType {
  using MO = OrderedTypeFacts<O>;
};

struct Coq_Pos {
  static Positive succ(const Positive &x);
  static Positive add(const Positive &x, const Positive &y);
  static Positive add_carry(const Positive &x, const Positive &y);
  static Positive pred_double(const Positive &x);
  static N pred_N(const Positive &x);

  struct mask {
    // TYPES
    struct IsNul {};

    struct IsPos {
      Positive a0;
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

    static mask ispos(Positive a0) { return mask(IsPos{std::move(a0)}); }

    static mask isneg() { return mask(IsNeg{}); }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    Comparison mask2cmp() const {
      if (std::holds_alternative<typename mask::IsNul>(this->v())) {
        return Comparison::EQ;
      } else if (std::holds_alternative<typename mask::IsPos>(this->v())) {
        return Comparison::GT;
      } else {
        return Comparison::LT;
      }
    }

    mask pred_mask() const {
      if (std::holds_alternative<typename mask::IsPos>(this->v())) {
        const auto &[a0] = std::get<typename mask::IsPos>(this->v());
        if (std::holds_alternative<typename Positive::XH>(a0.v())) {
          return mask::isnul();
        } else {
          return mask::ispos(pred(a0));
        }
      } else {
        return mask::isneg();
      }
    }

    mask double_mask() const {
      if (std::holds_alternative<typename mask::IsNul>(this->v())) {
        return mask::isnul();
      } else if (std::holds_alternative<typename mask::IsPos>(this->v())) {
        const auto &[a0] = std::get<typename mask::IsPos>(this->v());
        return mask::ispos(Positive::xo(a0));
      } else {
        return mask::isneg();
      }
    }

    mask succ_double_mask() const {
      if (std::holds_alternative<typename mask::IsNul>(this->v())) {
        return mask::ispos(Positive::xh());
      } else if (std::holds_alternative<typename mask::IsPos>(this->v())) {
        const auto &[a0] = std::get<typename mask::IsPos>(this->v());
        return mask::ispos(Positive::xi(a0));
      } else {
        return mask::isneg();
      }
    }

    template <typename T1, typename F1>
    T1 mask_rec(T1 f, F1 &&f0, T1 f1) const {
      return this->template mask_rect<T1>(std::move(f), f0, std::move(f1));
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, const Positive &>
    T1 mask_rect(T1 f, F1 &&f0, T1 f1) const {
      if (std::holds_alternative<typename mask::IsNul>(this->v())) {
        return f;
      } else if (std::holds_alternative<typename mask::IsPos>(this->v())) {
        const auto &[a0] = std::get<typename mask::IsPos>(this->v());
        return f0(a0);
      } else {
        return f1;
      }
    }
  };

  static mask double_pred_mask(const Positive &x);
  static mask sub_mask(const Positive &x, const Positive &y);
  static mask sub_mask_carry(const Positive &x, const Positive &y);
  static Positive sub(const Positive &x, const Positive &y);
  static Positive mul(const Positive &x, Positive y);

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, T1> &&
             std::is_invocable_r_v<T1, F0 &, const T1 &>
  static T1 iter(F0 &&f, const T1 &x, const Positive &n) {
    if (std::holds_alternative<typename Positive::XI>(n.v())) {
      const auto &[a0] = std::get<typename Positive::XI>(n.v());
      return f(iter<T1>(f, iter<T1>(f, x, *a0), *a0));
    } else if (std::holds_alternative<typename Positive::XO>(n.v())) {
      const auto &[a0] = std::get<typename Positive::XO>(n.v());
      return iter<T1>(f, iter<T1>(f, x, *a0), *a0);
    } else {
      return f(x);
    }
  }

  static Positive div2(const Positive &p);
  static Positive div2_up(const Positive &p);
  static Comparison compare_cont(Comparison r, const Positive &x,
                                 const Positive &y);
  static Comparison compare(const Positive &x0_, const Positive &x1_);
  static bool eqb(const Positive &p, const Positive &q);
  static bool leb(const Positive &x, const Positive &y);

  template <typename F0, typename F1>
  static std::pair<Positive, mask> sqrtrem_step(F0 &&f, F1 &&g,
                                                std::pair<Positive, mask> p) {
    auto [s, y] = std::move(p);
    if (std::holds_alternative<typename mask::IsPos>(y.v_mut())) {
      auto &[a0] = std::get<typename mask::IsPos>(y.v_mut());
      Positive s_ = Positive::xi(Positive::xo(s));
      Positive r_ = g(f(std::move(a0)));
      if (leb(s_, r_)) {
        return std::make_pair(Positive::xi(std::move(s)),
                              sub_mask(std::move(r_), std::move(s_)));
      } else {
        return std::make_pair(Positive::xo(std::move(s)),
                              mask::ispos(std::move(r_)));
      }
    } else {
      return std::make_pair(
          Positive::xo(std::move(s)),
          sub_mask(g(f(Positive::xh())),
                   Positive::xo(Positive::xo(Positive::xh()))));
    }
  }

  static std::pair<Positive, mask> sqrtrem(const Positive &p);
  static Positive sqrt(const Positive &p);
  static N Nsucc_double(const N &x);
  static N Ndouble(const N &n);
  static Positive lor(const Positive &p, const Positive &q);
  static N land(const Positive &p, const Positive &q);
  static N ldiff(const Positive &p, const Positive &q);
  static N lxor(const Positive &p, const Positive &q);

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, T1 &, T1> &&
             std::is_invocable_r_v<T1, F0 &, T1 &, T1 &>
  static T1 iter_op(F0 &&op, const Positive &p, T1 a) {
    if (std::holds_alternative<typename Positive::XI>(p.v())) {
      const auto &[a0] = std::get<typename Positive::XI>(p.v());
      return op(a, iter_op<T1>(op, *a0, op(a, a)));
    } else if (std::holds_alternative<typename Positive::XO>(p.v())) {
      const auto &[a0] = std::get<typename Positive::XO>(p.v());
      return iter_op<T1>(op, *a0, op(a, a));
    } else {
      return a;
    }
  }

  static uint64_t to_nat(const Positive &x);
  static Positive of_succ_nat(uint64_t n);
  using t = Positive;
  static Positive pred(const Positive &x);
  static Positive pow(const Positive &x, Positive x0_);
  static Positive square(const Positive &p);
  static uint64_t size_nat(const Positive &p);
  static Positive size(const Positive &p);
  static Positive min(Positive p, Positive p_);
  static Positive max(Positive p, Positive p_);
  static bool ltb(const Positive &x, const Positive &y);
  static Positive gcdn(uint64_t n, const Positive &a, const Positive &b);
  static Positive gcd(const Positive &a, const Positive &b);
  static std::pair<Positive, std::pair<Positive, Positive>>
  ggcdn(uint64_t n, const Positive &a, const Positive &b);
  static std::pair<Positive, std::pair<Positive, Positive>>
  ggcd(const Positive &a, const Positive &b);
  static Positive shiftl_nat(Positive p, uint64_t n);
  static Positive shiftr_nat(Positive p, uint64_t n);
  static Positive shiftl(Positive p, const N &n);
  static Positive shiftr(Positive p, const N &n);
  static bool testbit_nat(const Positive &p, uint64_t n);
  static bool testbit(const Positive &p, const N &n);
  static Positive of_nat(uint64_t n);
  static Positive of_uint_acc(const Uint &d, Positive acc);
  static N of_uint(const Uint &d);
  static Positive of_hex_uint_acc(const Uint0 &d, Positive acc);
  static N of_hex_uint(const Uint0 &d);
  static N of_num_uint(const Uint1 &d);
  static std::optional<Positive> of_int(const Signed_int &d);
  static std::optional<Positive> of_hex_int(const Signed_int0 &d);
  static std::optional<Positive> of_num_int(const Signed_int1 &d);
  static Uint to_little_uint(const Positive &p);
  static Uint to_uint(const Positive &p);
  static Uint0 to_little_hex_uint(const Positive &p);
  static Uint0 to_hex_uint(const Positive &p);
  static Uint1 to_num_uint(const Positive &p);
  static Uint1 to_num_hex_uint(const Positive &n);
  static Signed_int to_int(const Positive &n);
  static Signed_int0 to_hex_int(const Positive &p);
  static Signed_int1 to_num_int(const Positive &n);
  static Signed_int1 to_num_hex_int(const Positive &n);
  static bool eq_dec(const Positive &p, const Positive &x0);

  template <typename T1>
  static T1 peano_rect(T1 a,
                       std::type_identity_t<crane::fn<T1(Positive, T1)>> f,
                       const Positive &p) {
    crane::fn<T1(Positive)> f2 = [=](Positive _x0) -> T1 {
      return peano_rect<T1>(
          f(Positive::xh(), a),
          [=](const Positive &p0, const T1 &x) {
            return f(succ(Positive::xo(p0)), f(Positive::xo(p0), x));
          },
          _x0);
    };
    if (std::holds_alternative<typename Positive::XI>(p.v())) {
      const auto &[a0] = std::get<typename Positive::XI>(p.v());
      return f(Positive::xo(*a0), f2(*a0));
    } else if (std::holds_alternative<typename Positive::XO>(p.v())) {
      const auto &[a0] = std::get<typename Positive::XO>(p.v());
      return f2(*a0);
    } else {
      return a;
    }
  }

  template <typename T1, typename F1>
  static T1 peano_rec(const T1 &x0_, F1 &&x1_, const Positive &x2_) {
    return peano_rect<T1>(x0_, x1_, x2_);
  }

  struct PeanoView {
    // TYPES
    struct PeanoOne {};

    struct PeanoSucc {
      Positive p;
      std::shared_ptr<PeanoView> a1;
    };

    using variant_t = std::variant<PeanoOne, PeanoSucc>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    PeanoView() {}

    explicit PeanoView(PeanoOne _v) : v_(_v) {}

    explicit PeanoView(PeanoSucc _v) : v_(std::move(_v)) {}

    static PeanoView peanoone() { return PeanoView(PeanoOne{}); }

    static PeanoView peanosucc(Positive p, PeanoView a1) {
      return PeanoView(
          PeanoSucc{std::move(p), std::make_shared<PeanoView>(std::move(a1))});
    }

    // MANIPULATORS
    ~PeanoView() {
      auto _next = [&](variant_t &_v) -> std::shared_ptr<PeanoView> {
        if (auto *_alt = std::get_if<PeanoSucc>(&_v)) {
          if (_alt->a1 && _alt->a1.use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            return std::move(_alt->a1);
          }
        }
        return nullptr;
      };
      std::shared_ptr<PeanoView> _cur = _next(v_mut());
      while (_cur) {
        _cur = _next(_cur->v_mut());
      }
    }

    PeanoView(const PeanoView &) = default;
    PeanoView &operator=(const PeanoView &) = default;
    PeanoView(PeanoView &&) = default;
    PeanoView &operator=(PeanoView &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, Positive &, T1 &&>
    T1 PeanoView_iter(T1 a, F1 &&f, const Positive &_x) const {
      const PeanoView *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const PeanoView *_self;
        Positive _x;
      };

      /// CraneCont_PeanoSucc: saves [p], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_PeanoSucc {
        Positive p;
      };

      using CraneFrame = std::variant<CraneEnter, CraneCont_PeanoSucc>;
      T1 _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self, _x});
      /// Loopified PeanoView_iter: CraneEnter -> CraneCont_PeanoSucc.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const PeanoView *_self = _f._self;
          const Positive &_x = std::move(_f._x);
          auto &&_sv = *_self;
          if (std::holds_alternative<typename PeanoView::PeanoOne>(_sv.v())) {
            _result = a;
          } else {
            const auto &[p, a1] =
                std::get<typename PeanoView::PeanoSucc>(_sv.v());
            _stack.emplace_back(CraneCont_PeanoSucc{p});
            _stack.emplace_back(CraneEnter{crane_raw(a1), p});
          }
        } else {
          auto _f = std::move(std::get<CraneCont_PeanoSucc>(_frame));
          Positive p = std::move(_f.p);
          _result = f(p, std::move(_result));
        }
      }
      return _result;
    }

    PeanoView peanoView_xI(const Positive &) const {
      std::optional<PeanoView> _root{};
      std::shared_ptr<PeanoView> *_write = nullptr;
      const PeanoView *_loop_self = this;
      while (true) {
        auto &&_sv = *_loop_self;
        if (std::holds_alternative<typename PeanoView::PeanoOne>(_sv.v())) {
          auto _value = PeanoView::peanosucc(
              succ(Positive::xh()),
              PeanoView::peanosucc(Positive::xh(), PeanoView::peanoone()));
          (_write ? *(*_write = std::make_shared<PeanoView>(std::move(_value)))
                  : _root.emplace(std::move(_value)));
          break;
        } else {
          const auto &[p, a1] =
              std::get<typename PeanoView::PeanoSucc>(_sv.v());
          auto _cell1 = std::make_shared<PeanoView>(
              typename PeanoView::PeanoSucc(Positive::xi(p), nullptr));
          auto _cell = typename PeanoView::PeanoSucc(succ(Positive::xi(p)),
                                                     std::move(_cell1));
          PeanoView &_node =
              (_write
                   ? *(*_write = std::make_shared<PeanoView>(std::move(_cell)))
                   : _root.emplace(std::move(_cell)));
          _write = &std::get<typename PeanoView::PeanoSucc>(
                        std::get<typename PeanoView::PeanoSucc>(_node.v_mut())
                            .a1->v_mut())
                        .a1;
          _loop_self = crane_raw(a1);
          continue;
        }
      }
      return std::move(*_root);
    }

    PeanoView peanoView_xO(const Positive &) const {
      std::optional<PeanoView> _root{};
      std::shared_ptr<PeanoView> *_write = nullptr;
      const PeanoView *_loop_self = this;
      while (true) {
        auto &&_sv = *_loop_self;
        if (std::holds_alternative<typename PeanoView::PeanoOne>(_sv.v())) {
          auto _value =
              PeanoView::peanosucc(Positive::xh(), PeanoView::peanoone());
          (_write ? *(*_write = std::make_shared<PeanoView>(std::move(_value)))
                  : _root.emplace(std::move(_value)));
          break;
        } else {
          const auto &[p, a1] =
              std::get<typename PeanoView::PeanoSucc>(_sv.v());
          auto _cell1 = std::make_shared<PeanoView>(
              typename PeanoView::PeanoSucc(Positive::xo(p), nullptr));
          auto _cell = typename PeanoView::PeanoSucc(succ(Positive::xo(p)),
                                                     std::move(_cell1));
          PeanoView &_node =
              (_write
                   ? *(*_write = std::make_shared<PeanoView>(std::move(_cell)))
                   : _root.emplace(std::move(_cell)));
          _write = &std::get<typename PeanoView::PeanoSucc>(
                        std::get<typename PeanoView::PeanoSucc>(_node.v_mut())
                            .a1->v_mut())
                        .a1;
          _loop_self = crane_raw(a1);
          continue;
        }
      }
      return std::move(*_root);
    }

    template <typename T1, typename F1>
    T1 PeanoView_rec(T1 f, F1 &&f0, const Positive &_x) const {
      return this->template PeanoView_rect<T1>(std::move(f), f0, _x);
    }

    template <typename T1, typename F1>
    T1 PeanoView_rect(T1 f, F1 &&f0, const Positive &_x) const {
      const PeanoView *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const PeanoView *_self;
        Positive _x;
      };

      /// CraneCont_PeanoSucc: saves [p2, a1], resumes after recursive call,
      /// then processes rest.
      struct CraneCont_PeanoSucc {
        Positive p2;
        std::shared_ptr<PeanoView> a1;
      };

      using CraneFrame = std::variant<CraneEnter, CraneCont_PeanoSucc>;
      T1 _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self, _x});
      /// Loopified PeanoView_rect: CraneEnter -> CraneCont_PeanoSucc.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const PeanoView *_self = _f._self;
          const Positive &_x = std::move(_f._x);
          auto &&_sv = *_self;
          if (std::holds_alternative<typename PeanoView::PeanoOne>(_sv.v())) {
            _result = f;
          } else {
            const auto &[p2, a1] =
                std::get<typename PeanoView::PeanoSucc>(_sv.v());
            _stack.emplace_back(CraneCont_PeanoSucc{p2, a1});
            _stack.emplace_back(CraneEnter{crane_raw(a1), p2});
          }
        } else {
          auto _f = std::move(std::get<CraneCont_PeanoSucc>(_frame));
          Positive p2 = std::move(_f.p2);
          std::shared_ptr<PeanoView> a1 = std::move(_f.a1);
          _result = f0(p2, *a1, std::move(_result));
        }
      }
      return _result;
    }
  };

  static PeanoView peanoView(const Positive &p);
  static Reflect eqb_spec(const Positive &x, const Positive &y);
  static Comparison switch_Eq(Comparison c, Comparison c_);
  static Reflect leb_spec0(const Positive &x, const Positive &y);
  static Reflect ltb_spec0(const Positive &x, const Positive &y);

  struct Private_Tac {};

  struct Private_Dec {
    template <typename T1, typename F2>
      requires std::is_invocable_r_v<T1, F2 &, Positive &, Positive, const T1 &>
    static T1 max_case_strong(Positive n, Positive m0, F2 &&compat,
                              const T1 &hl, const T1 &hr) {
      CompareSpecT c =
          Datatypes::template CompSpec2Type<Positive>(n, m0, compare(n, m0));
      switch (c) {
      case CompareSpecT::COMPGTT: {
        return compat(n, max(n, std::move(m0)), hl);
      }
      default: {
        return compat(m0, max(std::move(n), m0), hr);
      }
      }
    }

    template <typename T1, typename F2>
    static T1 max_case(Positive n, Positive m0, F2 &&x, const T1 &x0,
                       const T1 &x1) {
      return max_case_strong<T1>(
          std::move(n), std::move(m0), x, [=]() { return x0; }(),
          [=]() { return x1; }());
    }

    static bool max_dec(Positive n, Positive m0);

    template <typename T1, typename F2>
      requires std::is_invocable_r_v<T1, F2 &, Positive &, Positive, const T1 &>
    static T1 min_case_strong(Positive n, Positive m0, F2 &&compat,
                              const T1 &hl, const T1 &hr) {
      CompareSpecT c =
          Datatypes::template CompSpec2Type<Positive>(n, m0, compare(n, m0));
      switch (c) {
      case CompareSpecT::COMPGTT: {
        return compat(m0, min(std::move(n), m0), hr);
      }
      default: {
        return compat(n, min(n, std::move(m0)), hl);
      }
      }
    }

    template <typename T1, typename F2>
    static T1 min_case(Positive n, Positive m0, F2 &&x, const T1 &x0,
                       const T1 &x1) {
      return min_case_strong<T1>(
          std::move(n), std::move(m0), x, [=]() { return x0; }(),
          [=]() { return x1; }());
    }

    static bool min_dec(Positive n, Positive m0);
  };

  template <typename T1>
  static T1 max_case_strong(Positive n, Positive m0, const T1 &x,
                            const T1 &x0) {
    return Private_Dec::template max_case_strong<T1>(
        std::move(n), std::move(m0),
        [](Positive, Positive, T1 x1) { return x1; }, x, x0);
  }

  template <typename T1>
  static T1 max_case(Positive n, Positive m0, const T1 &x, const T1 &x0) {
    return max_case_strong<T1>(
        std::move(n), std::move(m0), [=]() { return x; }(),
        [=]() { return x0; }());
  }

  static bool max_dec(const Positive &x0_, const Positive &x1_);

  template <typename T1>
  static T1 min_case_strong(Positive n, Positive m0, const T1 &x,
                            const T1 &x0) {
    return Private_Dec::template min_case_strong<T1>(
        std::move(n), std::move(m0),
        [](Positive, Positive, T1 x1) { return x1; }, x, x0);
  }

  template <typename T1>
  static T1 min_case(Positive n, Positive m0, const T1 &x, const T1 &x0) {
    return min_case_strong<T1>(
        std::move(n), std::move(m0), [=]() { return x; }(),
        [=]() { return x0; }());
  }

  static bool min_dec(const Positive &x0_, const Positive &x1_);
};

template <OrderedType X> struct Raw {
  using MX = OrderedTypeFacts<X>;
  using PX = KeyOrderedType<X>;
  using key = typename X::t;
  template <typename elt> using t = List<std::pair<typename X::t, elt>>;

  template <typename T1> static const t<T1> &empty() {
    static const t<T1> v = List<std::pair<typename X::t, T1>>::nil();
    return v;
  }

  template <typename T1>
  static bool is_empty(const List<std::pair<typename X::t, T1>> &l) {
    if (std::holds_alternative<
            typename List<std::pair<typename X::t, T1>>::Nil>(l.v())) {
      return true;
    } else {
      return false;
    }
  }

  template <typename T1>
  static bool mem(typename X::t k,
                  const List<std::pair<typename X::t, T1>> &s) {
    if (std::holds_alternative<
            typename List<std::pair<typename X::t, T1>>::Nil>(s.v())) {
      return false;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<std::pair<typename X::t, T1>>::Cons>(s.v());
      const auto &[k_, _x] = a0;
      auto &&_sv = X::compare(k, k_);
      if (std::holds_alternative<typename Compare<typename X::t>::LT>(
              _sv.v())) {
        return false;
      } else if (std::holds_alternative<typename Compare<typename X::t>::EQ>(
                     _sv.v())) {
        return true;
      } else {
        return mem<T1>(std::move(k), *a1);
      }
    }
  }

  template <typename T1>
  static std::optional<T1> find(typename X::t k,
                                const List<std::pair<typename X::t, T1>> &s) {
    if (std::holds_alternative<
            typename List<std::pair<typename X::t, T1>>::Nil>(s.v())) {
      return std::optional<T1>();
    } else {
      const auto &[a0, a1] =
          std::get<typename List<std::pair<typename X::t, T1>>::Cons>(s.v());
      const auto &[k_, x] = a0;
      auto &&_sv = X::compare(k, k_);
      if (std::holds_alternative<typename Compare<typename X::t>::LT>(
              _sv.v())) {
        return std::optional<T1>();
      } else if (std::holds_alternative<typename Compare<typename X::t>::EQ>(
                     _sv.v())) {
        return std::make_optional<T1>(x);
      } else {
        return find<T1>(std::move(k), *a1);
      }
    }
  }

  template <typename T1>
  static t<T1> add(typename X::t k, const T1 &x,
                   const List<std::pair<typename X::t, T1>> &s) {
    if (std::holds_alternative<
            typename List<std::pair<typename X::t, T1>>::Nil>(s.v())) {
      return List<std::pair<typename X::t, T1>>::cons(
          std::make_pair(std::move(k), x),
          List<std::pair<typename X::t, T1>>::nil());
    } else {
      const auto &[a0, a1] =
          std::get<typename List<std::pair<typename X::t, T1>>::Cons>(s.v());
      const auto &[k_, y] = a0;
      auto &&_sv = X::compare(k, k_);
      if (std::holds_alternative<typename Compare<typename X::t>::LT>(
              _sv.v())) {
        return List<std::pair<typename X::t, T1>>::cons(
            std::make_pair(std::move(k), x), s);
      } else if (std::holds_alternative<typename Compare<typename X::t>::EQ>(
                     _sv.v())) {
        return List<std::pair<typename X::t, T1>>::cons(
            std::make_pair(std::move(k), x), *a1);
      } else {
        return List<std::pair<typename X::t, T1>>::cons(
            std::make_pair(k_, y), add<T1>(std::move(k), x, *a1));
      }
    }
  }

  template <typename T1>
  static t<T1> remove(typename X::t k,
                      const List<std::pair<typename X::t, T1>> &s) {
    if (std::holds_alternative<
            typename List<std::pair<typename X::t, T1>>::Nil>(s.v())) {
      return List<std::pair<typename X::t, T1>>::nil();
    } else {
      const auto &[a0, a1] =
          std::get<typename List<std::pair<typename X::t, T1>>::Cons>(s.v());
      const auto &[k_, x] = a0;
      auto &&_sv = X::compare(k, k_);
      if (std::holds_alternative<typename Compare<typename X::t>::LT>(
              _sv.v())) {
        return s;
      } else if (std::holds_alternative<typename Compare<typename X::t>::EQ>(
                     _sv.v())) {
        return *a1;
      } else {
        return List<std::pair<typename X::t, T1>>::cons(
            std::make_pair(k_, x), remove<T1>(std::move(k), *a1));
      }
    }
  }

  template <typename T1>
  static t<T1> elements(List<std::pair<typename X::t, T1>> m0) {
    return m0;
  }

  template <typename T1, typename T2, typename F0>
  static T2 fold(F0 &&f, const List<std::pair<typename X::t, T1>> &m0, T2 acc) {
    if (std::holds_alternative<
            typename List<std::pair<typename X::t, T1>>::Nil>(m0.v())) {
      return acc;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<std::pair<typename X::t, T1>>::Cons>(m0.v());
      const auto &[k, e] = a0;
      return fold<T1, T2>(f, *a1, f(k, e, std::move(acc)));
    }
  }

  template <typename T1, typename F0>
  static bool equal(F0 &&cmp, const List<std::pair<typename X::t, T1>> &m0,
                    const List<std::pair<typename X::t, T1>> &m_) {
    if (std::holds_alternative<
            typename List<std::pair<typename X::t, T1>>::Nil>(m0.v())) {
      if (std::holds_alternative<
              typename List<std::pair<typename X::t, T1>>::Nil>(m_.v())) {
        return true;
      } else {
        return false;
      }
    } else {
      const auto &[a0, a1] =
          std::get<typename List<std::pair<typename X::t, T1>>::Cons>(m0.v());
      const auto &[x, e] = a0;
      if (std::holds_alternative<
              typename List<std::pair<typename X::t, T1>>::Nil>(m_.v())) {
        return false;
      } else {
        const auto &[a00, a10] =
            std::get<typename List<std::pair<typename X::t, T1>>::Cons>(m_.v());
        const auto &[x_, e_] = a00;
        auto &&_sv = X::compare(x, x_);
        if (std::holds_alternative<typename Compare<typename X::t>::EQ>(
                _sv.v())) {
          return (cmp(e, e_) && equal<T1>(cmp, *a1, *a10));
        } else {
          return false;
        }
      }
    }
  }

  template <typename T1, typename T2, typename F0>
  static t<T2> map(F0 &&f, const List<std::pair<typename X::t, T1>> &m0) {
    if (std::holds_alternative<
            typename List<std::pair<typename X::t, T1>>::Nil>(m0.v())) {
      return List<std::pair<typename X::t, T2>>::nil();
    } else {
      const auto &[a0, a1] =
          std::get<typename List<std::pair<typename X::t, T1>>::Cons>(m0.v());
      const auto &[k, e] = a0;
      return List<std::pair<typename X::t, T2>>::cons(std::make_pair(k, f(e)),
                                                      map<T1, T2>(f, *a1));
    }
  }

  template <typename T1, typename T2, typename F0>
  static t<T2> mapi(F0 &&f, const List<std::pair<typename X::t, T1>> &m0) {
    if (std::holds_alternative<
            typename List<std::pair<typename X::t, T1>>::Nil>(m0.v())) {
      return List<std::pair<typename X::t, T2>>::nil();
    } else {
      const auto &[a0, a1] =
          std::get<typename List<std::pair<typename X::t, T1>>::Cons>(m0.v());
      const auto &[k, e] = a0;
      return List<std::pair<typename X::t, T2>>::cons(
          std::make_pair(k, f(k, e)), mapi<T1, T2>(f, *a1));
    }
  }

  template <typename T1>
  static List<std::pair<key, T1>>
  option_cons(typename X::t k, const std::optional<T1> &o,
              List<std::pair<typename X::t, T1>> l) {
    if (o.has_value()) {
      const T1 &e = *o;
      return List<std::pair<typename X::t, T1>>::cons(
          std::make_pair(std::move(k), e), std::move(l));
    } else {
      return l;
    }
  }

  template <typename T1, typename T2, typename T3, typename F0>
  static t<T3> map2_l(F0 &&f, const List<std::pair<typename X::t, T1>> &m0) {
    if (std::holds_alternative<
            typename List<std::pair<typename X::t, T1>>::Nil>(m0.v())) {
      return List<std::pair<typename X::t, T3>>::nil();
    } else {
      const auto &[a0, a1] =
          std::get<typename List<std::pair<typename X::t, T1>>::Cons>(m0.v());
      const auto &[k, e] = a0;
      return option_cons<T3>(k,
                             f(std::make_optional<T1>(e), std::optional<T2>()),
                             map2_l<T1, T2, T3>(f, *a1));
    }
  }

  template <typename T1, typename T2, typename T3, typename F0>
  static t<T3> map2_r(F0 &&f, const List<std::pair<typename X::t, T2>> &m_) {
    if (std::holds_alternative<
            typename List<std::pair<typename X::t, T2>>::Nil>(m_.v())) {
      return List<std::pair<typename X::t, T3>>::nil();
    } else {
      const auto &[a0, a1] =
          std::get<typename List<std::pair<typename X::t, T2>>::Cons>(m_.v());
      const auto &[k, e_] = a0;
      return option_cons<T3>(k,
                             f(std::optional<T1>(), std::make_optional<T2>(e_)),
                             map2_r<T1, T2, T3>(f, *a1));
    }
  }

  template <typename T1, typename T2, typename T3>
  static t<T3> map2(const std::type_identity_t<crane::fn<std::optional<T3>(
                        std::optional<T1>, std::optional<T2>)>> &f,
                    List<std::pair<typename X::t, T1>> m0, t<T2> x0_) {
    if (std::holds_alternative<
            typename List<std::pair<typename X::t, T1>>::Nil>(m0.v_mut())) {
      return map2_r<T1, T2, T3>(f, std::move(x0_));
    } else {
      auto &[a0, a1] =
          std::get<typename List<std::pair<typename X::t, T1>>::Cons>(
              m0.v_mut());
      const auto &[k, e] = a0;
      auto map2_aux_impl = [&](auto &_self_map2_aux,
                               const List<std::pair<typename X::t, T2>> &m_)
          -> List<std::pair<typename X::t, T3>> {
        if (std::holds_alternative<
                typename List<std::pair<typename X::t, T2>>::Nil>(m_.v())) {
          return map2_l<T1, T2, T3>(f, m0);
        } else {
          const auto &[a00, a10] =
              std::get<typename List<std::pair<typename X::t, T2>>::Cons>(
                  m_.v());
          const auto &[k_, e_] = a00;
          auto &&_sv = X::compare(k, k_);
          if (std::holds_alternative<typename Compare<typename X::t>::LT>(
                  _sv.v())) {
            return option_cons<T3>(
                k, f(std::make_optional<T1>(e), std::optional<T2>()),
                map2<T1, T2, T3>(f, *a1, m_));
          } else if (std::holds_alternative<
                         typename Compare<typename X::t>::EQ>(_sv.v())) {
            return option_cons<T3>(
                k, f(std::make_optional<T1>(e), std::make_optional<T2>(e_)),
                map2<T1, T2, T3>(f, *a1, *a10));
          } else {
            return option_cons<T3>(
                k_, f(std::optional<T1>(), std::make_optional<T2>(e_)),
                _self_map2_aux(_self_map2_aux, *a10));
          }
        }
      };
      auto map2_aux = [&](const List<std::pair<typename X::t, T2>> &m_)
          -> List<std::pair<typename X::t, T3>> {
        return map2_aux_impl(map2_aux_impl, m_);
      };
      return map2_aux(std::move(x0_));
    }
  }

  template <typename T1, typename T2>
  static t<std::pair<std::optional<T1>, std::optional<T2>>>
  combine(const List<std::pair<typename X::t, T1>> &m0, t<T2> x0_) {
    if (std::holds_alternative<
            typename List<std::pair<typename X::t, T1>>::Nil>(m0.v())) {
      return map<T2, std::pair<std::optional<T1>, std::optional<T2>>>(
          [](const T2 &e_) {
            return std::make_pair(std::optional<T1>(),
                                  std::make_optional<T2>(e_));
          },
          std::move(x0_));
    } else {
      const auto &[a0, a1] =
          std::get<typename List<std::pair<typename X::t, T1>>::Cons>(m0.v());
      const List<std::pair<typename X::t, T1>> &a1_value = *a1;
      const auto &[k, e] = a0;
      auto combine_aux_impl = [&](auto &_self_combine_aux,
                                  const List<std::pair<typename X::t, T2>> &m_)
          -> List<std::pair<typename X::t,
                            std::pair<std::optional<T1>, std::optional<T2>>>> {
        if (std::holds_alternative<
                typename List<std::pair<typename X::t, T2>>::Nil>(m_.v())) {
          return map<T1, std::pair<std::optional<T1>, std::optional<T2>>>(
              [](const T1 &e0) {
                return std::make_pair(std::make_optional<T1>(e0),
                                      std::optional<T2>());
              },
              m0);
        } else {
          const auto &[a00, a10] =
              std::get<typename List<std::pair<typename X::t, T2>>::Cons>(
                  m_.v());
          const auto &[k_, e_] = a00;
          auto &&_sv = X::compare(k, k_);
          if (std::holds_alternative<typename Compare<typename X::t>::LT>(
                  _sv.v())) {
            return List<
                std::pair<typename X::t,
                          std::pair<std::optional<T1>, std::optional<T2>>>>::
                cons(std::make_pair(k, std::make_pair(std::make_optional<T1>(e),
                                                      std::optional<T2>())),
                     combine<T1, T2>(a1_value, m_));
          } else if (std::holds_alternative<
                         typename Compare<typename X::t>::EQ>(_sv.v())) {
            return List<
                std::pair<typename X::t,
                          std::pair<std::optional<T1>, std::optional<T2>>>>::
                cons(std::make_pair(k,
                                    std::make_pair(std::make_optional<T1>(e),
                                                   std::make_optional<T2>(e_))),
                     combine<T1, T2>(a1_value, *a10));
          } else {
            return List<
                std::pair<typename X::t,
                          std::pair<std::optional<T1>, std::optional<T2>>>>::
                cons(std::make_pair(k_,
                                    std::make_pair(std::optional<T1>(),
                                                   std::make_optional<T2>(e_))),
                     _self_combine_aux(_self_combine_aux, *a10));
          }
        }
      };
      auto combine_aux = [&](const List<std::pair<typename X::t, T2>> &m_)
          -> List<std::pair<typename X::t,
                            std::pair<std::optional<T1>, std::optional<T2>>>> {
        return combine_aux_impl(combine_aux_impl, m_);
      };
      return combine_aux(std::move(x0_));
    }
  }

  template <typename T1, typename T2, typename T3>
  static T3
  fold_right_pair(const std::type_identity_t<crane::fn<T3(T1, T2, T3)>> &f,
                  const List<std::pair<T1, T2>> &l, T3 i) {
    return l.template fold_right<T3>(
        [=](const std::pair<T1, T2> &p, const T3 &eta0_) {
          return [=](T3 _pa0) { return f(p.first, p.second, _pa0); }(eta0_);
        },
        std::move(i));
  }

  template <typename T1, typename T2, typename T3>
  static List<std::pair<key, T3>>
  map2_alt(const std::type_identity_t<crane::fn<
               std::optional<T3>(std::optional<T1>, std::optional<T2>)>> &f,
           const List<std::pair<typename X::t, T1>> &m0,
           const List<std::pair<typename X::t, T2>> &m_) {
    List<std::pair<typename X::t,
                   std::pair<std::optional<T1>, std::optional<T2>>>>
        m1 = combine<T1, T2>(m0, m_);
    List<std::pair<typename X::t, std::optional<T3>>> m2 =
        map<std::pair<std::optional<T1>, std::optional<T2>>, std::optional<T3>>(
            [=](const std::pair<std::optional<T1>, std::optional<T2>> &p) {
              return f(p.first, p.second);
            },
            std::move(m1));
    return fold_right_pair<key, std::optional<T3>, List<std::pair<key, T3>>>(
        option_cons<T3>, std::move(m2), List<std::pair<key, T3>>::nil());
  }

  template <typename T1, typename T2>
  static std::optional<std::pair<std::optional<T1>, std::optional<T2>>>
  at_least_one(const std::optional<T1> &o, const std::optional<T2> &o_) {
    if (o.has_value()) {
      const T1 &_x = *o;
      return std::make_optional<
          std::pair<std::optional<T1>, std::optional<T2>>>(
          std::make_pair(o, o_));
    } else {
      if (o_.has_value()) {
        const T2 &_x = *o_;
        return std::make_optional<
            std::pair<std::optional<T1>, std::optional<T2>>>(
            std::make_pair(o, o_));
      } else {
        return std::optional<std::pair<std::optional<T1>, std::optional<T2>>>();
      }
    }
  }

  template <typename T1, typename T2, typename T3, typename F0>
  static std::optional<T3> at_least_one_then_f(F0 &&f,
                                               const std::optional<T1> &o,
                                               const std::optional<T2> &o_) {
    if (o.has_value()) {
      const T1 &_x = *o;
      return f(o, o_);
    } else {
      if (o_.has_value()) {
        const T2 &_x = *o_;
        return f(o, o_);
      } else {
        return std::optional<T3>();
      }
    }
  }
};

template <OrderedType X> struct Make {
  using Raw = Raw<X>;
  using E = X;
  using key = typename E::t;

  template <typename elt> struct slist {
    typename Raw::template t<elt> this_;

    // ACCESSORS
    template <typename CraneU> operator slist<CraneU>() const {
      return {crane_convert<typename Raw::template t<CraneU>>(this_)};
    }
  };

  template <typename elt> using t = slist<elt>;

  template <typename T1> static const t<T1> &empty() {
    static const t<T1> v = slist<T1>{Raw::template empty<T1>()};
    return v;
  }

  template <typename T1> static bool is_empty(const slist<T1> &m0) {
    return Raw::template is_empty<T1>(m0.this_);
  }

  template <typename T1>
  static t<T1> add(typename X::t x, const T1 &e, const slist<T1> &m0) {
    return slist<T1>{Raw::template add<T1>(std::move(x), e, m0.this_)};
  }

  template <typename T1>
  static std::optional<T1> find(typename X::t x, const slist<T1> &m0) {
    return Raw::template find<T1>(std::move(x), m0.this_);
  }

  template <typename T1>
  static t<T1> remove(typename X::t x, const slist<T1> &m0) {
    return slist<T1>{Raw::template remove<T1>(std::move(x), m0.this_)};
  }

  template <typename T1> static bool mem(typename X::t x, const slist<T1> &m0) {
    return Raw::template mem<T1>(std::move(x), m0.this_);
  }

  template <typename T1, typename T2, typename F0>
  static t<T2> map(F0 &&f, const slist<T1> &m0) {
    return slist<T2>{Raw::template map<T1, T2>(f, m0.this_)};
  }

  template <typename T1, typename T2, typename F0>
  static t<T2> mapi(F0 &&f, const slist<T1> &m0) {
    return slist<T2>{Raw::template mapi<T1, T2>(f, m0.this_)};
  }

  template <typename T1, typename T2, typename T3, typename F0>
  static t<T3> map2(F0 &&f, const slist<T1> &m0, const slist<T2> &m_) {
    return slist<T3>{Raw::template map2<T1, T2, T3>(f, m0.this_, m_.this_)};
  }

  template <typename T1>
  static List<std::pair<key, T1>> elements(const slist<T1> &m0) {
    return Raw::template elements<T1>(m0.this_);
  }

  template <typename T1> static uint64_t cardinal(const slist<T1> &m0) {
    return m0.this_.length();
  }

  template <typename T1, typename T2, typename F0>
  static T2 fold(F0 &&f, const slist<T1> &m0, const T2 &i) {
    return Raw::template fold<T1, T2>(f, m0.this_, i);
  }

  template <typename T1, typename F0>
  static bool equal(F0 &&cmp, const slist<T1> &m0, const slist<T1> &m_) {
    return Raw::template equal<T1>(cmp, m0.this_, m_.this_);
  }
};

struct Positive_as_OT {
  using t = Positive;
  static Compare<Positive> compare(const Positive &x, const Positive &y);
  static bool eq_dec(const Positive &x0_, const Positive &x1_);
};

using Coq_Positive_as_OT = Coq_Pos;

struct SameNamedFileModules {
  using PM = Make<Positive_as_OT>;
  using P2 = Coq_Positive_as_OT;
  static inline const PM::template t<uint64_t> m = PM::template add<uint64_t>(
      Positive::xh(), UINT64_C(2), PM::template empty<uint64_t>());
  static inline const uint64_t found = []() -> uint64_t {
    auto _cs = PM::template find<uint64_t>(Positive::xh(), m);
    if (_cs.has_value()) {
      const uint64_t &v = *_cs;
      return v;
    } else {
      return UINT64_C(0);
    }
  }();
  static inline const bool larger =
      Coq_Pos::eqb(P2::max(Positive::xi(Positive::xh()),
                           Positive::xo(Positive::xo(Positive::xh()))),
                   Positive::xo(Positive::xo(Positive::xh())));
};

template <typename T1>
CompSpecT<T1> Datatypes::CompSpec2Type(const T1 &, const T1 &, Comparison x0_) {
  return Datatypes::CompareSpec2Type(x0_);
}

#endif // INCLUDED_SAME_NAMED_FILE_MODULES
