#ifndef INCLUDED_REUSE_LIST_SHAPES
#define INCLUDED_REUSE_LIST_SHAPES

#include <cstdint>
#include <memory>
#include <stdexcept>
#include <type_traits>
#include <utility>
#define CRANE_NON_ATOMIC_RC 1
#include "crane_fn.h"
#include "crane_variant.h"
#include "field.h"
#include "obj.h"
#include "rc.h"
#include "small_vector.h"

template <typename A> struct List;
enum class Comparison;
struct Positive;
struct N;

template <typename A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    crane::field<A> a;
    crane::rc<List<A>> l;
  };

  using variant_t = crane::variant<Nil, Cons>;

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
          if (crane::holds_alternative<typename List<CraneU>::Nil>(
                  _other.v())) {
            return Nil{};
          } else {
            const auto &[a, l] =
                crane::get<typename List<CraneU>::Cons>(_other.v());
            return Cons{[&]() -> A {
                          if constexpr (crane_convertible<A, const CraneU &>) {
                            return crane_convert<A>(crane::unbox(a));
                          } else {
                            throw std::logic_error(
                                "unreachable: inactive constructor field at "
                                "this instantiation");
                          }
                        }(),
                        (l ? crane::make_rc<List<A>>(crane_convert<List<A>>(*l))
                           : nullptr)};
          }
        }()) {}

  static List<A> nil() { return List<A>(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List<A>(Cons{crane::field<A>(std::move(a)),
                        crane::make_rc<List<A>>(std::move(l))});
  }

  static List<A> cons_crane_reuse(crane::rc<List<A>> _tok, A a, List<A> l) {
    return List<A>(
        Cons{crane::field<A>(std::move(a)),
             crane::make_rc_reusing<List<A>>(std::move(_tok), std::move(l))});
  }

  // MANIPULATORS
  ~List() {
    auto _next = [&](variant_t &_v) -> crane::rc<List<A>> {
      if (auto *_alt = crane::get_if<Cons>(&_v)) {
        if (_alt->l && _alt->l.use_count() == 1) {
          return std::move(_alt->l);
        }
      }
      return nullptr;
    };
    crane::rc<List<A>> _cur = _next(v_mut());
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

  template <typename T1> List<std::pair<A, T1>> combine(List<T1> l_) const {
    crane::rc<List<std::pair<A, T1>>> _head{};
    crane::rc<List<std::pair<A, T1>>> *_write = &_head;
    const List<A> *_loop_self = this;
    const List<T1> *_loop_l_ = &l_;
    while (true) {
      auto &&_sv = *_loop_self;
      if (crane::holds_alternative<typename List<A>::Nil>(_sv.v())) {
        *_write = crane::make_rc<List<std::pair<A, T1>>>(
            List<std::pair<A, T1>>::nil());
        break;
      } else {
        const auto &[a0, a1] = crane::get<typename List<A>::Cons>(_sv.v());
        if (crane::holds_alternative<typename List<T1>::Nil>(_loop_l_->v())) {
          *_write = crane::make_rc<List<std::pair<A, T1>>>(
              List<std::pair<A, T1>>::nil());
          break;
        } else {
          const auto &[a00, a10] =
              crane::get<typename List<T1>::Cons>(_loop_l_->v());
          auto _cell = crane::make_rc<List<std::pair<A, T1>>>(
              typename List<std::pair<A, T1>>::Cons(
                  std::make_pair(crane::unbox(a0), crane::unbox(a00)),
                  nullptr));
          *_write = std::move(_cell);
          _write = &crane::get<typename List<std::pair<A, T1>>::Cons>(
                        (*_write)->v_mut())
                        .l;
          _loop_self = crane_raw(a1);
          _loop_l_ = crane_raw(a10);
          continue;
        }
      }
    }
    return std::move(*_head);
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, T1 &&, A>
  T1 fold_left(F0 &&f, T1 a0) const {
    const List<A> *_loop_self = this;
    T1 _loop_a0 = std::move(a0);
    while (true) {
      auto &&_sv = *_loop_self;
      if (crane::holds_alternative<typename List<A>::Nil>(_sv.v())) {
        return _loop_a0;
      } else {
        const auto &[a1, a2] = crane::get<typename List<A>::Cons>(_sv.v());
        _loop_self = crane_raw(a2);
        _loop_a0 = f(std::move(_loop_a0), crane::unbox(a1));
      }
    }
  }

  List<A> firstn(uint64_t n) const {
    crane::rc<List<A>> _head{};
    crane::rc<List<A>> *_write = &_head;
    const List<A> *_loop_self = this;
    uint64_t _loop_n = n;
    while (true) {
      if (_loop_n <= 0) {
        *_write = crane::make_rc<List<A>>(List<A>::nil());
        break;
      } else {
        uint64_t n0 = _loop_n - 1;
        auto &&_sv = *_loop_self;
        if (crane::holds_alternative<typename List<A>::Nil>(_sv.v())) {
          *_write = crane::make_rc<List<A>>(List<A>::nil());
          break;
        } else {
          const auto &[a0, a1] = crane::get<typename List<A>::Cons>(_sv.v());
          auto _cell = crane::make_rc<List<A>>(
              typename List<A>::Cons(crane::unbox(a0), nullptr));
          *_write = std::move(_cell);
          _write = &crane::get<typename List<A>::Cons>((*_write)->v_mut()).l;
          _loop_self = crane_raw(a1);
          _loop_n = n0;
          continue;
        }
      }
    }
    return std::move(*_head);
  }
};
enum class Comparison { EQ, LT, GT };

struct Positive {
  // TYPES
  struct XI {
    crane::rc<Positive> a0;
  };

  struct XO {
    crane::rc<Positive> a0;
  };

  struct XH {};

  using variant_t = crane::variant<XI, XO, XH>;

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
    return Positive(XI{crane::make_rc<Positive>(std::move(a0))});
  }

  static Positive xi_crane_reuse(crane::rc<Positive> _tok, Positive a0) {
    return Positive(
        XI{crane::make_rc_reusing<Positive>(std::move(_tok), std::move(a0))});
  }

  static Positive xo(Positive a0) {
    return Positive(XO{crane::make_rc<Positive>(std::move(a0))});
  }

  static Positive xo_crane_reuse(crane::rc<Positive> _tok, Positive a0) {
    return Positive(
        XO{crane::make_rc_reusing<Positive>(std::move(_tok), std::move(a0))});
  }

  static Positive xh() { return Positive(XH{}); }

  // MANIPULATORS
  ~Positive() {
    auto _next = [&](variant_t &_v) -> crane::rc<Positive> {
      if (auto *_alt = crane::get_if<XI>(&_v)) {
        if (_alt->a0 && _alt->a0.use_count() == 1) {
          return std::move(_alt->a0);
        }
      }
      if (auto *_alt = crane::get_if<XO>(&_v)) {
        if (_alt->a0 && _alt->a0.use_count() == 1) {
          return std::move(_alt->a0);
        }
      }
      return nullptr;
    };
    crane::rc<Positive> _cur = _next(v_mut());
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
    crane::rc<Positive> a0;
  };

  using variant_t = crane::variant<N0, Npos>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  N() {}

  explicit N(N0 _v) : v_(_v) {}

  explicit N(Npos _v) : v_(std::move(_v)) {}

  static N n0() { return N(N0{}); }

  static N npos(Positive a0) {
    return N(Npos{crane::make_rc<Positive>(std::move(a0))});
  }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct Pos {
  static Positive pred_double(Positive x);

  struct mask {
    // TYPES
    struct IsNul {};

    struct IsPos {
      crane::rc<Positive> a0;
    };

    struct IsNeg {};

    using variant_t = crane::variant<IsNul, IsPos, IsNeg>;

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

    static mask ispos(Positive a0) {
      return mask(IsPos{crane::make_rc<Positive>(std::move(a0))});
    }

    static mask isneg() { return mask(IsNeg{}); }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  static mask succ_double_mask(mask x);
  static mask double_mask(mask x);
  static mask double_pred_mask(const Positive &x);
  static mask sub_mask(const Positive &x, const Positive &y);
  static mask sub_mask_carry(const Positive &x, const Positive &y);
  static Comparison compare_cont(Comparison r, const Positive &x,
                                 const Positive &y);
  static Comparison compare(const Positive &x0_, const Positive &x1_);

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, T1 &, T1> &&
             std::is_invocable_r_v<T1, F0 &, T1 &, T1 &>
  static T1 iter_op(F0 &&op, const Positive &p, T1 a) {
    if (crane::holds_alternative<typename Positive::XI>(p.v())) {
      const auto &[a0] = crane::get<typename Positive::XI>(p.v());
      return op(a, iter_op<T1>(op, *a0, op(a, a)));
    } else if (crane::holds_alternative<typename Positive::XO>(p.v())) {
      const auto &[a0] = crane::get<typename Positive::XO>(p.v());
      return iter_op<T1>(op, *a0, op(a, a));
    } else {
      return a;
    }
  }

  static uint64_t to_nat(const Positive &x);
};

struct BinNat {
  static N succ_double(N x);
  static N double_(N n);
  static N sub(N n, N m);
  static Comparison compare(const N &n, const N &m);
  static bool leb(const N &x, const N &y);
  static std::pair<N, N> pos_div_eucl(const Positive &a, N b);
  static std::pair<N, N> div_eucl(const N &a, N b);
  static N div(const N &a, N b);
  static uint64_t to_nat(const N &a);
};

struct ReuseListShapes {
  static inline const List<std::pair<uint64_t, uint64_t>> zipped =
      List<uint64_t>::cons(
          UINT64_C(1),
          List<uint64_t>::cons(
              UINT64_C(2),
              List<uint64_t>::cons(UINT64_C(3), List<uint64_t>::nil())))
          .template combine<uint64_t>(List<uint64_t>::cons(
              UINT64_C(10),
              List<uint64_t>::cons(
                  UINT64_C(20),
                  List<uint64_t>::cons(
                      UINT64_C(30),
                      List<uint64_t>::cons(UINT64_C(40),
                                           List<uint64_t>::nil())))));
  static inline const List<uint64_t> firsts =
      List<uint64_t>::cons(
          UINT64_C(5),
          List<uint64_t>::cons(
              UINT64_C(6),
              List<uint64_t>::cons(UINT64_C(7), List<uint64_t>::nil())))
          .firstn(UINT64_C(2));
  static List<uint64_t> bump(List<uint64_t> l);
  static List<uint64_t> take(uint64_t n, List<uint64_t> l);
  static List<uint64_t> ins(uint64_t k, List<uint64_t> s);

  struct frames {
    // TYPES
    struct Single {
      crane::rc<List<uint64_t>> a0;
    };

    struct Push {
      crane::rc<List<uint64_t>> a0;
      crane::rc<frames> a1;
    };

    using variant_t = crane::variant<Single, Push>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    frames() {}

    explicit frames(Single _v) : v_(std::move(_v)) {}

    explicit frames(Push _v) : v_(std::move(_v)) {}

    static frames single(List<uint64_t> a0) {
      return frames(Single{crane::make_rc<List<uint64_t>>(std::move(a0))});
    }

    static frames push(List<uint64_t> a0, frames a1) {
      return frames(Push{crane::make_rc<List<uint64_t>>(std::move(a0)),
                         crane::make_rc<frames>(std::move(a1))});
    }

    static frames push_crane_reuse(crane::rc<frames> _tok, List<uint64_t> a0,
                                   frames a1) {
      return frames(
          Push{crane::make_rc<List<uint64_t>>(std::move(a0)),
               crane::make_rc_reusing<frames>(std::move(_tok), std::move(a1))});
    }

    // MANIPULATORS
    ~frames() {
      auto _next = [&](variant_t &_v) -> crane::rc<frames> {
        if (auto *_alt = crane::get_if<Push>(&_v)) {
          if (_alt->a1 && _alt->a1.use_count() == 1) {
            return std::move(_alt->a1);
          }
        }
        return nullptr;
      };
      crane::rc<frames> _cur = _next(v_mut());
      while (_cur) {
        _cur = _next(_cur->v_mut());
      }
    }

    frames(const frames &) = default;
    frames &operator=(const frames &) = default;
    frames(frames &&) = default;
    frames &operator=(frames &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F0, typename F1>
  static T1 frames_rect(F0 &&f, F1 &&f0, const frames &f1) {
    if (crane::holds_alternative<typename frames::Single>(f1.v())) {
      const auto &[a0] = crane::get<typename frames::Single>(f1.v());
      return f(*a0);
    } else {
      const auto &[a0, a1] = crane::get<typename frames::Push>(f1.v());
      return f0(*a0, *a1, frames_rect<T1>(f, f0, *a1));
    }
  }

  template <typename T1, typename F0, typename F1>
  static T1 frames_rec(F0 &&f, F1 &&f0, const frames &f1) {
    return frames_rect<T1>(f, f0, f1);
  }

  struct mem {
    frames stack;
    uint64_t top;
  };

  static frames add_to_frame(const mem &m, uint64_t k);
  static frames add_to_frame_(const mem &m, uint64_t k);
  static inline const uint64_t result =
      (((((((zipped.template fold_left<uint64_t>(
                 [](uint64_t acc, const std::pair<uint64_t, uint64_t> &pat) {
                   const auto &[a, b] = pat;
                   return ((acc + a) + b);
                 },
                 UINT64_C(0)) +
             firsts.template fold_left<uint64_t>(
                 [](uint64_t _x0, uint64_t _x1) -> uint64_t {
                   return (_x0 + _x1);
                 },
                 UINT64_C(0))) +
            bump(List<uint64_t>::cons(
                     UINT64_C(1),
                     List<uint64_t>::cons(UINT64_C(2), List<uint64_t>::nil())))
                .template fold_left<uint64_t>(
                    [](uint64_t _x0, uint64_t _x1) -> uint64_t {
                      return (_x0 + _x1);
                    },
                    UINT64_C(0))) +
           []() {
             auto &&_sv = add_to_frame(
                 mem{frames::push(List<uint64_t>::cons(UINT64_C(1),
                                                       List<uint64_t>::nil()),
                                  frames::single(List<uint64_t>::cons(
                                      UINT64_C(2), List<uint64_t>::nil()))),
                     UINT64_C(0)},
                 UINT64_C(7));
             if (crane::holds_alternative<typename frames::Single>(_sv.v())) {
               return UINT64_C(0);
             } else {
               const auto &[a0, a1] =
                   crane::get<typename frames::Push>(_sv.v());
               const List<uint64_t> &a0_value = *a0;
               return a0_value.template fold_left<uint64_t>(
                   [](uint64_t _x0, uint64_t _x1) -> uint64_t {
                     return (_x0 + _x1);
                   },
                   UINT64_C(0));
             }
           }()) +
          take(UINT64_C(2),
               List<uint64_t>::cons(
                   UINT64_C(4),
                   List<uint64_t>::cons(
                       UINT64_C(5), List<uint64_t>::cons(
                                        UINT64_C(6), List<uint64_t>::nil()))))
              .template fold_left<uint64_t>(
                  [](uint64_t _x0, uint64_t _x1) -> uint64_t {
                    return (_x0 + _x1);
                  },
                  UINT64_C(0))) +
         []() {
           auto &&_sv0 =
               add_to_frame_(mem{frames::single(List<uint64_t>::cons(
                                     UINT64_C(3), List<uint64_t>::nil())),
                                 UINT64_C(0)},
                             UINT64_C(9));
           if (crane::holds_alternative<typename frames::Single>(_sv0.v())) {
             const auto &[a00] = crane::get<typename frames::Single>(_sv0.v());
             const List<uint64_t> &a00_value = *a00;
             return a00_value.template fold_left<uint64_t>(
                 [](uint64_t _x0, uint64_t _x1) -> uint64_t {
                   return (_x0 + _x1);
                 },
                 UINT64_C(0));
           } else {
             return UINT64_C(0);
           }
         }()) +
        BinNat::to_nat(BinNat::div(
            N::npos(Positive::xo(Positive::xo(Positive::xo(
                Positive::xi(Positive::xo(Positive::xi(Positive::xi(
                    Positive::xi(Positive::xi(Positive::xh())))))))))),
            N::npos(Positive::xi(Positive::xi(Positive::xh())))))) +
       ins(UINT64_C(1),
           ins(UINT64_C(4),
               ins(UINT64_C(2), ins(UINT64_C(3), List<uint64_t>::nil()))))
           .template fold_left<uint64_t>(
               [](uint64_t _x0, uint64_t _x1) -> uint64_t {
                 return (_x0 + _x1);
               },
               UINT64_C(0)));
};

#endif // INCLUDED_REUSE_LIST_SHAPES
