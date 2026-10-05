#ifndef INCLUDED_OBJECT_MODEL
#define INCLUDED_OBJECT_MODEL

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include <algorithm>
#include <atomic>
#include <concepts>
#include <crane_itree.h>
#include <cstdint>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

struct nat_ix;
struct nat_ix_stref;
template <typename A> struct List;
template <typename Err> struct ExceptE;
struct Err;
struct STRefNat;
template <typename S> struct Point;
template <typename S> struct Account;
template <typename S> struct BankAccountCollection;
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

struct Z {};

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
};

template <typename Err> struct ExceptE {
  // DATA
  Err a0;

  // ACCESSORS
  ExceptE<Err> clone() const { return {a0}; }

  template <typename CraneU> operator ExceptE<CraneU>() const {
    return {[&]() -> CraneU {
      if constexpr (crane_convertible<CraneU, const Err &>) {
        return crane_convert<CraneU>(a0);
      } else {
        throw std::logic_error(
            "unreachable: inactive constructor field at this instantiation");
      }
    }()};
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

struct nat_ix {
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

static_assert(Ix<nat_ix, uint64_t>);

struct STRefNat {
  // DATA
  uint64_t s;

  // ACCESSORS
  STRefNat clone() const { return {s}; }

  // CREATORS
  static STRefNat mkstref(uint64_t s) { return {s}; }

  uint64_t STRefToIxNat() const;
};

struct nat_ix_stref {
  static crane::obj mkSTRef(uint64_t x) { return STRefNat::mkstref(x); }

  static uint64_t STRefToIx(crane::obj _p_a0) {
    STRefNat a0 = crane::any_cast<STRefNat>(_p_a0);
    return a0.STRefToIxNat();
  }
};

static_assert(STRefClass<nat_ix_stref, uint64_t>);

template <typename S> struct Point {
  crane::fn<int64_t(std::monostate)> getX;
  crane::fn<void(int64_t)> moveD;
  crane::fn<int64_t(std::monostate)> offsetX;

  // ACCESSORS
  template <typename CraneU> operator Point<CraneU>() const {
    return {crane_convert<crane::fn<int64_t(std::monostate)>>(getX), moveD,
            crane_convert<crane::fn<int64_t(std::monostate)>>(offsetX)};
  }
};

template <typename S> struct Account {
  crane::fn<int64_t(std::monostate)> getBalance;
  crane::fn<int64_t(uint64_t)> deposit;
  crane::fn<std::optional<int64_t>(int64_t)> withdraw;

  // ACCESSORS
  template <typename CraneU> operator Account<CraneU>() const {
    return {
        crane_convert<crane::fn<int64_t(std::monostate)>>(getBalance),
        crane_convert<crane::fn<int64_t(uint64_t)>>(deposit),
        crane_convert<crane::fn<std::optional<int64_t>(int64_t)>>(withdraw)};
  }
};

template <typename S> struct BankAccountCollection {
  Account<S> checking;
  Account<S> saving;

  // ACCESSORS
  template <typename CraneU> operator BankAccountCollection<CraneU>() const {
    return {crane_convert<Account<CraneU>>(checking),
            crane_convert<Account<CraneU>>(saving)};
  }
};

std::pair<std::pair<int64_t, int64_t>, int64_t> testtoST1_ext();
std::pair<std::pair<std::pair<int64_t, int64_t>, int64_t>, int64_t>
testtoST2_ext();
std::pair<std::pair<std::pair<int64_t, int64_t>, bool>, int64_t>
acc_test1_ext();
std::pair<std::pair<std::pair<int64_t, bool>, int64_t>, int64_t>
acc_test2_ext();
std::pair<std::pair<std::pair<int64_t, bool>, int64_t>, int64_t>
bankacc_test1_ext();

inline uint64_t STRefNat::STRefToIxNat() const {
  const auto &[s] = *this;
  return s;
}

#endif // INCLUDED_OBJECT_MODEL
