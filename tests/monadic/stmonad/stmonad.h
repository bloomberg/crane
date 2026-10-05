#ifndef INCLUDED_STMONAD
#define INCLUDED_STMONAD

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include "small_vector.h"
#include <algorithm>
#include <atomic>
#include <concepts>
#include <crane_itree.h>
#include <cstdint>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <type_traits>
#include <utility>
#include <variant>

template <typename A> struct List;
template <typename Err> struct ExceptE;
struct Err;
struct STRefNat;
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
template <typename I, typename T>
concept STRefClass = requires {
  { I::mkSTRef(std::declval<T>()) } -> std::convertible_to<crane::obj>;
  { I::STRefToIx(std::declval<crane::obj>()) } -> std::convertible_to<T>;
};

struct ListDef {
  static List<uint64_t> seq(uint64_t start, uint64_t len);
};

struct Nat {};

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
      : v_(crane_convert_spine(
            _other, std::shared_ptr<List<A>>(nullptr),
            [](const List<CraneU> &_cell) -> const List<CraneU> * {
              if (std::holds_alternative<typename List<CraneU>::Cons>(
                      _cell.v())) {
                return std::get<typename List<CraneU>::Cons>(_cell.v()).l.get();
              } else {
                return nullptr;
              }
            },
            [&](const List<CraneU> &_other,
                std::shared_ptr<List<A>> _below) -> variant_t {
              if (std::holds_alternative<typename List<CraneU>::Nil>(
                      _other.v())) {
                return Nil{};
              } else {
                const auto &[a, l] =
                    std::get<typename List<CraneU>::Cons>(_other.v());
                return Cons{
                    [&]() -> A {
                      if constexpr (crane_convertible<A, const CraneU &>) {
                        return crane_convert<A>(a);
                      } else {
                        throw std::logic_error(
                            "unreachable: inactive constructor field at this "
                            "instantiation");
                      }
                    }(),
                    std::move(_below)};
              }
            },
            [](auto &&_alt) {
              return std::make_shared<List<A>>(std::move(_alt));
            })) {}

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

  template <typename F0> List<A> filter(F0 &&f) const {
    std::optional<List<A>> _root{};
    std::shared_ptr<List<A>> *_write = nullptr;
    const List<A> *_loop_self = this;
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
        auto _value = List<A>::nil();
        (_write ? *(*_write = std::make_shared<List<A>>(std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[a0, a1] = std::get<typename List<A>::Cons>(_sv.v());
        if (f(a0)) {
          auto _cell = typename List<A>::Cons(a0, nullptr);
          List<A> &_node =
              (_write ? *(*_write = std::make_shared<List<A>>(std::move(_cell)))
                      : _root.emplace(std::move(_cell)));
          _write = &std::get<typename List<A>::Cons>(_node.v_mut()).l;
          _loop_self = crane_raw(a1);
          continue;
        } else {
          _loop_self = crane_raw(a1);
          continue;
        }
      }
    }
    return std::move(*_root);
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

  List<A> app(List<A> m) const {
    std::optional<List<A>> _root{};
    std::shared_ptr<List<A>> *_write = nullptr;
    const List<A> *_loop_self = this;
    List<A> _loop_m = std::move(m);
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
        auto _value = std::move(_loop_m);
        (_write ? *(*_write = std::make_shared<List<A>>(std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[a0, a1] = std::get<typename List<A>::Cons>(_sv.v());
        auto _cell = typename List<A>::Cons(a0, nullptr);
        List<A> &_node =
            (_write ? *(*_write = std::make_shared<List<A>>(std::move(_cell)))
                    : _root.emplace(std::move(_cell)));
        _write = &std::get<typename List<A>::Cons>(_node.v_mut()).l;
        _loop_self = crane_raw(a1);
        continue;
      }
    }
    return std::move(*_root);
  }
};

template <typename Err> struct ExceptE {
  // DATA
  Err a0;

  // ACCESSORS
  ExceptE<Err> clone() const { return {a0}; }

  template <typename CraneU>
    requires crane_convertible<CraneU, const Err &>
  operator ExceptE<CraneU>() const {
    return {crane_convert<CraneU>(a0)};
  }

  // CREATORS
  static ExceptE<Err> Throw_(Err a0) { return {std::move(a0)}; }
};

struct Err {
  // DATA
  std::string x;

  // ACCESSORS
  Err clone() const { return {x}; }

  // CREATORS
  static Err error(std::string x) { return {std::move(x)}; }
};

struct STMonadExamples {
  template <typename F1>
    requires std::is_invocable_r_v<List<uint64_t>, F1 &, List<uint64_t>>
  static List<uint64_t> quicksort_fun_functional(const List<uint64_t> &l,
                                                 F1 &&quicksort_fun0);
};

struct STRefNat {
  // DATA
  uint64_t s;

  // ACCESSORS
  STRefNat clone() const { return {s}; }

  // CREATORS
  static STRefNat mkstref(uint64_t s) { return {s}; }

  uint64_t STRefToIxNat() const;
};

struct STMonadTests {
  struct nat_idx {
    static List<uint64_t> range(uint64_t fp, uint64_t sp) {
      auto &&_once1 = (UINT64_C(1) + sp);
      return ListDef::seq(fp, (((_once1 - fp) > _once1 ? 0 : (_once1 - fp))));
    }

    static std::optional<uint64_t> index(uint64_t fp, uint64_t sp, uint64_t i) {
      if ((fp <= i && i <= sp)) {
        return std::make_optional<uint64_t>((((i - fp) > i ? 0 : (i - fp))));
      } else {
        return std::optional<uint64_t>();
      }
    }

    constexpr static uint64_t rangeSize(uint64_t fp, uint64_t sp) {
      auto &&_once2 = (UINT64_C(1) + sp);
      return (((_once2 - fp) > _once2 ? 0 : (_once2 - fp)));
    }

    constexpr static uint64_t toNat(uint64_t n) { return n; }

    constexpr static uint64_t fromNat(uint64_t n) { return n; }

    constexpr static uint64_t suc(uint64_t x) { return (x + 1); }

    constexpr static uint64_t sub(uint64_t a0, uint64_t a1) {
      return (((a0 - a1) > a0 ? 0 : (a0 - a1)));
    }

    constexpr static uint64_t max(uint64_t a0, uint64_t a1) {
      return std::max(a0, a1);
    }

    constexpr static uint64_t zero() { return UINT64_C(0); }
  };

  static_assert(Ix<nat_idx, uint64_t>);

  struct nat_stref {
    static crane::obj mkSTRef(uint64_t x) { return STRefNat::mkstref(x); }

    static uint64_t STRefToIx(crane::obj _p_a0) {
      STRefNat a0 = crane::any_cast<STRefNat>(_p_a0);
      return a0.STRefToIxNat();
    }
  };

  static_assert(STRefClass<nat_stref, uint64_t>);
  static uint64_t array_simp_fixed_init();
  static std::pair<std::pair<uint64_t, uint64_t>, List<uint64_t>>
  array_simp_list();

  template <typename _tcI0, typename _tcI1>
    requires STRefClass<_tcI0, uint64_t> && Ix<_tcI1, uint64_t>
  static uint64_t fib_ST(uint64_t n) {
    if (n < UINT64_C(2)) {
      return n;
    } else {
      std::shared_ptr<uint64_t> x;
      x = std::make_shared<decltype(UINT64_C(0))>(UINT64_C(0));
      std::shared_ptr<uint64_t> y;
      y = std::make_shared<decltype(UINT64_C(1))>(UINT64_C(1));
      auto fib_loop = [](uint64_t k, std::shared_ptr<uint64_t> x0,
                         std::shared_ptr<uint64_t> y0, uint64_t,
                         uint64_t) -> uint64_t {
        uint64_t _loop_k = k;
        while (true) {
          if (_loop_k <= 0) {
            return *x0;
          } else {
            uint64_t k_ = _loop_k - 1;
            uint64_t x_ = *x0;
            uint64_t y_ = *y0;
            *x0 = y_;
            *y0 = (x_ + y_);
            _loop_k = k_;
          }
        }
      };
      return fib_loop(n, x, y, _tcI1::zero(), _tcI1::suc(_tcI1::zero()));
    }
  }

  static uint64_t fib_fun(uint64_t n);
  static uint64_t nth(uint64_t n, const List<uint64_t> &l, uint64_t default0);

  template <typename _tcI0, typename _tcI1>
    requires STRefClass<_tcI0, uint64_t> && Ix<_tcI1, uint64_t>
  static std::pair<bool, bool> new_and_read_both_bool() {
    auto r1 = false;
    auto r2 = true;
    bool x1 = std::move(r1);
    bool x2 = std::move(r2);
    return std::make_pair(x1, x2);
  }

  template <typename _tcI0, typename _tcI1>
    requires STRefClass<_tcI0, uint64_t> && Ix<_tcI1, uint64_t>
  static std::pair<uint64_t, uint64_t> new_and_read_both_nat() {
    auto r1 = UINT64_C(5);
    auto r2 = UINT64_C(6);
    uint64_t x1 = std::move(r1);
    uint64_t x2 = std::move(r2);
    return std::make_pair(x1, x2);
  }

  template <typename _tcI0, typename _tcI1>
    requires STRefClass<_tcI0, uint64_t> && Ix<_tcI1, uint64_t>
  static uint64_t tree_simp_another_nat() {
    auto v = UINT64_C(5);
    v = UINT64_C(6);
    return v;
  }

  template <typename _tcI0, typename _tcI1>
    requires STRefClass<_tcI0, uint64_t> && Ix<_tcI1, uint64_t>
  static bool tree_simp_bool() {
    auto v = true;
    return v;
  }

  template <typename _tcI0, typename _tcI1>
    requires STRefClass<_tcI0, uint64_t> && Ix<_tcI1, uint64_t>
  static uint64_t tree_simp_nat() {
    auto v = UINT64_C(5);
    return v;
  }

  static List<uint64_t> quicksort_fun(const List<uint64_t> &x);
  static List<uint64_t> quicksort_ST_mine(const List<uint64_t> &xs);
  static std::string list_to_string_helper(const List<uint64_t> &l);
  static std::string list_to_string(const List<uint64_t> &l);
  static List<uint64_t> rep_list_nat(List<uint64_t> l, uint64_t n);
  static inline const List<uint64_t> input_lst1 = List<uint64_t>::cons(
      UINT64_C(212498),
      List<uint64_t>::cons(
          UINT64_C(127),
          List<uint64_t>::cons(
              UINT64_C(5981),
              List<uint64_t>::cons(
                  UINT64_C(2749812),
                  List<uint64_t>::cons(
                      UINT64_C(74879),
                      List<uint64_t>::cons(
                          UINT64_C(126),
                          List<uint64_t>::cons(
                              UINT64_C(4),
                              List<uint64_t>::cons(
                                  UINT64_C(51),
                                  List<uint64_t>::cons(
                                      UINT64_C(2412),
                                      List<uint64_t>::cons(
                                          UINT64_C(10645),
                                          List<uint64_t>::nil()))))))))));
  static std::string test_quicksort_ST(std::monostate _x);
  static std::string test_quicksort_fun(std::monostate _x);
};

template <typename F1>
  requires std::is_invocable_r_v<List<uint64_t>, F1 &, List<uint64_t>>
List<uint64_t>
STMonadExamples::quicksort_fun_functional(const List<uint64_t> &l,
                                          F1 &&quicksort_fun0) {
  if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
    return List<uint64_t>::nil();
  } else {
    const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
    const List<uint64_t> &a1_value = *a1;
    return quicksort_fun0(a1_value.filter([=](uint64_t x) { return x < a0; }))
        .app(List<uint64_t>::cons(a0, List<uint64_t>::nil())
                 .app(quicksort_fun0(
                     a1_value.filter([=](uint64_t x) { return a0 <= x; }))));
  }
}

inline uint64_t STRefNat::STRefToIxNat() const {
  const auto &[s] = *this;
  return s;
}

#endif // INCLUDED_STMONAD
