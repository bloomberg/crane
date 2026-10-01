#ifndef INCLUDED_BORROWED_FIELD_MOVED_INTO_METHOD
#define INCLUDED_BORROWED_FIELD_MOVED_INTO_METHOD

#include "crane_fn.h"
#include "obj.h"
#include "small_vector.h"
#include <any>
#include <atomic>
#include <concepts>
#include <memory>
#include <optional>
#include <stdexcept>
#include <utility>
#include <variant>

struct Nat;
template <typename A> struct List;
enum class Comparison;
struct Positive;
struct N;
struct Z;

struct Coq_Pos {
  static Positive succ(const Positive &x);
  static Positive add(const Positive &x, const Positive &y);
  static Positive add_carry(const Positive &x, const Positive &y);
  static Positive mul(const Positive &x, Positive y);
};

struct Nat {
  // TYPES
  struct O {};

  struct S {
    std::shared_ptr<Nat> a0;
  };

  using variant_t = std::variant<O, S>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Nat() {}

  explicit Nat(O _v) : v_(_v) {}

  explicit Nat(S _v) : v_(std::move(_v)) {}

  static Nat o() { return Nat(O{}); }

  static Nat s(Nat a0) { return Nat(S{std::make_shared<Nat>(std::move(a0))}); }

  // MANIPULATORS
  ~Nat() {
    auto _next = [&](variant_t &_v) -> std::shared_ptr<Nat> {
      if (auto *_alt = std::get_if<S>(&_v)) {
        if (_alt->a0 && _alt->a0.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          return std::move(_alt->a0);
        }
      }
      return nullptr;
    };
    std::shared_ptr<Nat> _cur = _next(v_mut());
    while (_cur) {
      _cur = _next(_cur->v_mut());
    }
  }

  Nat(const Nat &) = default;
  Nat &operator=(const Nat &) = default;
  Nat(Nat &&) noexcept = default;
  Nat &operator=(Nat &&) noexcept = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

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

  template <typename _U>
  List(const List<_U> &_other)
      : v_([&]() -> variant_t {
          if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
            return Nil{};
          } else {
            const auto &[a, l] = std::get<typename List<_U>::Cons>(_other.v());
            return Cons{
                [&]() -> A {
                  if constexpr (crane_convertible<A, const _U &>) {
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
  List(List &&) noexcept = default;
  List &operator=(List &&) noexcept = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};
enum class Comparison { EQ, LT, GT };

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
  Positive(Positive &&) noexcept = default;
  Positive &operator=(Positive &&) noexcept = default;

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

struct Z {
  // TYPES
  struct Z0 {};

  struct Zpos {
    Positive a0;
  };

  struct Zneg {
    Positive a0;
  };

  using variant_t = std::variant<Z0, Zpos, Zneg>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Z() {}

  explicit Z(Z0 _v) : v_(_v) {}

  explicit Z(Zpos _v) : v_(std::move(_v)) {}

  explicit Z(Zneg _v) : v_(std::move(_v)) {}

  static Z z0() { return Z(Z0{}); }

  static Z zpos(Positive a0) { return Z(Zpos{std::move(a0)}); }

  static Z zneg(Positive a0) { return Z(Zneg{std::move(a0)}); }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct Pos {
  static Positive succ(const Positive &x);
  static Positive add(const Positive &x, const Positive &y);
  static Positive add_carry(const Positive &x, const Positive &y);
  static Positive pred_double(const Positive &x);

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

  static mask succ_double_mask(const mask &x);
  static mask double_mask(const mask &x);
  static mask double_pred_mask(const Positive &x);
  static mask sub_mask(const Positive &x, const Positive &y);
  static mask sub_mask_carry(const Positive &x, const Positive &y);
  static Positive mul(const Positive &x, Positive y);
  static Comparison compare_cont(Comparison r, const Positive &x,
                                 const Positive &y);
  static Comparison compare(const Positive &x0_, const Positive &x1_);
  static bool eqb(const Positive &p, const Positive &q);
  static Positive of_succ_nat(const Nat &n);
};

struct BinNat {
  static N succ_double(const N &x);
  static N double_(const N &n);
  static N sub(N n, const N &m);
  static Comparison compare(const N &n, const N &m);
  static bool leb(const N &x, const N &y);
  static std::pair<N, N> pos_div_eucl(const Positive &a, const N &b);
  static N mul(const N &n, const N &m);
  static std::pair<N, N> div_eucl(const N &a, const N &b);
  static N div(const N &a, const N &b);
};

struct BinInt {
  static Z double_(const Z &x);
  static Z succ_double(const Z &x);
  static Z pred_double(const Z &x);
  static Z pos_sub(const Positive &x, const Positive &y);
  static Z add(Z x, Z y);
  static Z mul(const Z &x, const Z &y);
  static bool eqb(const Z &x, const Z &y);
  static Z of_nat(const Nat &n);
  static Z of_N(const N &n);
};

/// walk recurses into the element type ta of an array type, and adds
/// size_of ta into the offset on the way.  ta is a field of the borrowed
/// parameter t (const ty &); ty's recursive field is a shared_ptr, so
/// the element node is shared with whoever built t -- here the global
/// arr.
///
/// The call is emitted as _tcI0::size_of(std::move( *t0)): the last read of
/// ta is moved into the by-value class method.  That hollows out the element
/// node of arr itself, so the second walk over arr reads a moved-from
/// positive (an XO whose child is null) and segfaults.
///
/// It takes a class with three methods.  With Size cut to one or two
/// methods the same call is emitted as size_of( *t0), no move.  It also
/// takes the let k := ...: without it, no move.
///
/// Found in Vellvm's Gep.handle_gep_h (its Sizeof class has three
/// methods): a loop executing one getelementptr twice segfaulted on the
/// second, in N.div under Sizeof_dtyp.
///
/// Size lives in its own module only because in one module Crane emits the
/// Size concept after the struct whose template uses it (a separate,
/// smaller problem).
struct BfmTypes {
  struct ty {
    // TYPES
    struct TB {
      Positive n;
    };

    struct TS {
      bool packed;
      std::shared_ptr<List<ty>> fields;
    };

    struct TA {
      bool vector;
      N sz;
      std::shared_ptr<ty> t;
    };

    using variant_t = std::variant<TB, TS, TA>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    ty() {}

    explicit ty(TB _v) : v_(std::move(_v)) {}

    explicit ty(TS _v) : v_(std::move(_v)) {}

    explicit ty(TA _v) : v_(std::move(_v)) {}

    static ty tb(Positive n) { return ty(TB{std::move(n)}); }

    static ty ts(bool packed, List<ty> fields) {
      return ty(TS{packed, std::make_shared<List<ty>>(std::move(fields))});
    }

    static ty ta(bool vector, N sz, ty t) {
      return ty(TA{vector, std::move(sz), std::make_shared<ty>(std::move(t))});
    }

    // MANIPULATORS
    ~ty() {
      crane::small_vector<std::shared_ptr<ty>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<TS>(&_v)) {
          if (_alt->fields && _alt->fields.use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            auto _lp = _alt->fields.get();
            while (std::holds_alternative<typename List<ty>::Cons>(_lp->v())) {
              auto &_lc = std::get<typename List<ty>::Cons>(_lp->v_mut());
              _stack.push_back(std::make_shared<ty>(std::move(_lc.a)));
              if (_lc.l && _lc.l.use_count() == 1) {
                std::atomic_thread_fence(std::memory_order_acquire);
                _lp = _lc.l.get();
              } else {
                break;
              }
            }
            _alt->fields.reset();
          }
        }
        if (auto *_alt = std::get_if<TA>(&_v)) {
          if (_alt->t && _alt->t.use_count() == 1) {
            _stack.push_back(std::move(_alt->t));
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

    ty(const ty &) = default;
    ty &operator=(const ty &) = default;
    ty(ty &&) noexcept = default;
    ty &operator=(ty &&) noexcept = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };
};

template <typename I>
concept Size = requires {
  { I::bit_size_of(std::declval<BfmTypes::ty>()) } -> std::convertible_to<N>;
  { I::size_of(std::declval<BfmTypes::ty>()) } -> std::convertible_to<N>;
  { I::align_of(std::declval<BfmTypes::ty>()) } -> std::convertible_to<N>;
};

struct BorrowedFieldMovedIntoMethod {
  template <Size _tcI0>
  static std::optional<Z> walk(const BfmTypes::ty &t, const Z &off,
                               const List<Nat> &vs) {
    if (std::holds_alternative<typename List<Nat>::Nil>(vs.v())) {
      return std::make_optional<Z>(off);
    } else {
      const auto &[a0, a1] = std::get<typename List<Nat>::Cons>(vs.v());
      Z k = BinInt::of_nat(a0);
      if (std::holds_alternative<typename BfmTypes::ty::TA>(t.v())) {
        const auto &[vector0, sz0, t0] =
            std::get<typename BfmTypes::ty::TA>(t.v());
        return walk<_tcI0>(
            *t0,
            BinInt::add(off, BinInt::mul(std::move(k),
                                         BinInt::of_N(_tcI0::size_of(*t0)))),
            *a1);
      } else {
        return std::optional<Z>();
      }
    }
  }

  static N sz(const BfmTypes::ty &t);

  struct SizeI {
    static N bit_size_of(BfmTypes::ty t) {
      return BinNat::mul(
          N::npos(Positive::xo(Positive::xo(Positive::xo(Positive::xh())))),
          sz(std::move(t)));
    }

    static N size_of(BfmTypes::ty a0) { return sz(std::move(a0)); }

    static N align_of(BfmTypes::ty a0) { return sz(std::move(a0)); }
  };

  static_assert(Size<SizeI>);
  static inline const BfmTypes::ty arr = BfmTypes::ty::ta(
      false, N::npos(Positive::xo(Positive::xo(Positive::xh()))),
      BfmTypes::ty::tb(Positive::xo(Positive::xo(Positive::xo(
          Positive::xo(Positive::xo(Positive::xo(Positive::xh()))))))));

  static Z get(const std::optional<Z> &o);
  /// Each walk is 3 * 8 = 24.
  static bool check(std::monostate _x);
};

#endif // INCLUDED_BORROWED_FIELD_MOVED_INTO_METHOD
