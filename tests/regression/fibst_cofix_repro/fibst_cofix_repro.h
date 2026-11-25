#pragma once

#include "crane_fn.h"
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
#include <string_view>
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

  static List<A> cons(A a, crane::shared_child_slot<List<A>> l) {
    return List<A>(Cons{std::move(a), l.take()});
  }

  // MANIPULATORS
  ~List() {
    // Release the children this node alone owns in a loop, not recursively, so
    // a deep value cannot overflow the stack.
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
        throw std::logic_error("unreachable: inactive constructor field at "
                               "this instantiation");
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

struct STRefNat {
  // DATA
  uint64_t s;

  // ACCESSORS
  STRefNat clone() const { return {s}; }

  // CREATORS
  static STRefNat mkstref(uint64_t s) { return {s}; }

  uint64_t STRefToIxNat() const;
};

/// Reproduces a version of fibST in STMonadtest.v.  It recurses without
/// end by construction: n is not decremented on each recursive call.
/// The test checks that the divergence is a constant-stack loop.
///
/// Extraction used to fail with "a type mapped to nothing reached the
/// printer: STEvent".  Three defects: the section's Lets are lets at
/// the head of the body, and db_from_rel_context numbered them as type
/// variables, so the annotation of go named no variable of the
/// declaration and seeded nothing; a let cofix was not seeded from its
/// annotation at all (only a let fix was); and seeding opened every
/// Unknown of an annotation to a meta, including the argument the
/// unapplied family STEvent ... +' exceptE Err is eta-expanded at,
/// which nothing solves.  The open metas generalised into type variables
/// of go's own, so go was lifted to a template whose call spelled the
/// skipped STEvent.  Then, generated in place, Core_plan.Closures
/// took go to escape, as a cofixpoint's body is suspended -- but a
/// cofixpoint into a monad generated as sequencing is not.
template <typename _tcI0, typename _tcI1, typename T1>
  requires STRefClass<_tcI0, T1> && Ix<_tcI1, T1>
uint64_t fibst_repro(uint64_t n) {
  auto go =
      [&](const std::shared_ptr<uint64_t> &x,
          const std::shared_ptr<uint64_t> &y, const T1 &,
          const T1 &)
           -> uint64_t {
        // Loop replaces the tail recursion: each recursive call updates the
        // loop variables.
        while (true) {
          if (n <= 0) {
            return *x;
          } else {
            uint64_t _x = n - 1;
            uint64_t x_ = *x;
            uint64_t y_ = *y;
            *x = y_;
            *y = (x_ + y_);
          }
        }
      };
  if (n <= UINT64_C(2)) {
    return n;
  } else {
    std::shared_ptr<uint64_t> x = std::make_shared<uint64_t>(UINT64_C(0));
    std::shared_ptr<uint64_t> y = std::make_shared<uint64_t>(UINT64_C(1));
    return go(std::move(x), std::move(y), _tcI1::zero(),
              _tcI1::suc(_tcI1::zero()));
  }
}

struct FibstCofixReproTests {
  struct nat_idx {
    static List<uint64_t> range(uint64_t fp, uint64_t sp) {
      auto _once1 = (UINT64_C(1) + sp);
      return ListDef::seq(fp, (((_once1 - fp) > _once1 ? 0 : (_once1 - fp))));
    }

    constexpr static std::optional<uint64_t> index(uint64_t fp, uint64_t sp,
                                                   uint64_t i) {
      if ((fp <= i && i <= sp)) {
        return std::make_optional<uint64_t>((((i - fp) > i ? 0 : (i - fp))));
      } else {
        return std::optional<uint64_t>();
      }
    }

    constexpr static uint64_t rangeSize(uint64_t fp, uint64_t sp) {
      auto _once2 = (UINT64_C(1) + sp);
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
};

inline uint64_t STRefNat::STRefToIxNat() const {
  const auto &[s] = *this;
  return s;
}
