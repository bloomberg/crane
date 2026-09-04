#ifndef INCLUDED_GLOBAL_STATE
#define INCLUDED_GLOBAL_STATE

#include "crane_fn.h"
#include "small_vector.h"
#include <algorithm>
#include <any>
#include <atomic>
#include <concepts>
#include <crane_globals.h>
#include <memory>
#include <optional>
#include <string>
#include <utility>
#include <variant>

template <typename A> struct List;
template <typename Err> struct ExceptE;
struct Err;
struct GlobRefNat;

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

  template <typename _U> List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      this->v_ = Nil{};
    } else {
      const auto &[a, l] = std::get<typename List<_U>::Cons>(_other.v());
      this->v_ = Cons{[&]() -> A {
                        if constexpr (std::is_same_v<_U, std::any>)
                          return crane_any_cast<A>(a);
                        else
                          return A(a);
                      }(),
                      (l ? std::make_shared<List<A>>(*l) : nullptr)};
    }
  }

  static List<A> nil() { return List<A>(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List<A>(Cons{std::move(a), std::make_shared<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  ~List() {
    crane::small_vector<std::shared_ptr<List<A>>> _stack = {};
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
        std::atomic_thread_fence(std::memory_order_acquire);
        _drain(_cur->v_mut());
      }
    }
  }

  List(const List &) = default;
  List &operator=(const List &) = default;
  List(List &&) noexcept = default;
  List &operator=(List &&) noexcept = default;

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

struct ListDef {
  static List<uint64_t> seq(uint64_t start, uint64_t len);
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

struct Err {
  // DATA
  std::string x;

  // ACCESSORS
  Err clone() const { return {x}; }

  // CREATORS
  static Err error(std::string x) { return {std::move(x)}; }
};

struct GlobalStateExamples {
  template <typename _tcI0, typename T1>
    requires Ix<_tcI0, T1>
  static T1 idx_x();
  template <typename _tcI0, typename T1>
    requires Ix<_tcI0, T1>
  static T1 idx_y();
  template <typename _tcI0, typename T1>
    requires Ix<_tcI0, T1>
  static T1 ctr_idx();
};

template <typename I, typename T>
concept GlobRefClass = requires {
  { I::mkGlobRef(std::declval<T>()) } -> std::convertible_to<std::any>;
  { I::GlobRefToIx(std::declval<std::any>()) } -> std::convertible_to<T>;
};

struct GlobRefNat {
  // DATA
  uint64_t a;

  // ACCESSORS
  GlobRefNat clone() const { return {a}; }

  // CREATORS
  static GlobRefNat mkglobref(uint64_t a) { return {a}; }

  uint64_t GlobRefToIxNat() const {
    const auto &[a] = *this;
    return a;
  }
};

struct GlobalStateTests {
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
    static std::any mkGlobRef(uint64_t x) { return GlobRefNat::mkglobref(x); }

    static uint64_t GlobRefToIx(std::any _p_a0) {
      GlobRefNat a0 = std::any_cast<GlobRefNat>(_p_a0);
      return a0.GlobRefToIxNat();
    }
  };

  static_assert(GlobRefClass<nat_stref, uint64_t>);

  template <typename _tcI0, typename _tcI1>
    requires GlobRefClass<_tcI0, uint64_t> && Ix<_tcI1, uint64_t>
  static std::pair<uint64_t, uint64_t> new_and_read_both_nat() {
    uint64_t r1 = (_crane_globals[_tcI1::zero()] = UINT64_C(5), _tcI1::zero());
    uint64_t r2 = (_crane_globals[_tcI1::suc(_tcI1::zero())] = UINT64_C(6),
                   _tcI1::suc(_tcI1::zero()));
    uint64_t x1 = std::any_cast<uint64_t>(_crane_globals.at(r1));
    uint64_t x2 = std::any_cast<uint64_t>(_crane_globals.at(r2));
    return std::make_pair(x1, x2);
  }

  template <typename _tcI0, typename _tcI1>
    requires GlobRefClass<_tcI0, uint64_t> && Ix<_tcI1, uint64_t>
  static uint64_t fib_Glob(uint64_t n) {
    if (n < UINT64_C(2)) {
      return n;
    } else {
      uint64_t x = (_crane_globals[_tcI1::zero()] = UINT64_C(0), _tcI1::zero());
      uint64_t y = (_crane_globals[_tcI1::suc(_tcI1::zero())] = UINT64_C(1),
                    _tcI1::suc(_tcI1::zero()));
      auto fib_loop_impl = [](auto &, uint64_t k, uint64_t x0,
                              uint64_t y0) -> uint64_t {
        uint64_t _loop_k = std::move(k);
        while (true) {
          if (_loop_k <= 0) {
            return std::any_cast<uint64_t>(_crane_globals.at(x0));
          } else {
            uint64_t k_ = _loop_k - 1;
            uint64_t x_ = std::any_cast<uint64_t>(_crane_globals.at(x0));
            uint64_t y_ = std::any_cast<uint64_t>(_crane_globals.at(y0));
            _crane_globals[x0] = y_;
            _crane_globals[y0] = (x_ + y_);
            _loop_k = k_;
          }
        }
      };
      auto fib_loop = [&](uint64_t k, uint64_t x0, uint64_t y0) -> uint64_t {
        return fib_loop_impl(fib_loop_impl, k, x0, y0);
      };
      return fib_loop(n, x, y);
    }
  }

  static uint64_t fib_fun(uint64_t n);
  static uint64_t counter();
  static uint64_t counter_next_mine(uint64_t ctr);
  static std::string gensym(uint64_t counter0, std::string prefix);
};

template <typename _tcI0, typename T1>
  requires Ix<_tcI0, T1>
T1 GlobalStateExamples::idx_x() {
  return _tcI0::zero();
}

template <typename _tcI0, typename T1>
  requires Ix<_tcI0, T1>
T1 GlobalStateExamples::idx_y() {
  return _tcI0::suc(_tcI0::zero());
}

template <typename _tcI0, typename T1>
  requires Ix<_tcI0, T1>
T1 GlobalStateExamples::ctr_idx() {
  return _tcI0::suc(_tcI0::suc(_tcI0::zero()));
}

#endif // INCLUDED_GLOBAL_STATE
