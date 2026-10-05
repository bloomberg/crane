#ifndef INCLUDED_EPOCH_CELL_GLYPH_TRACE
#define INCLUDED_EPOCH_CELL_GLYPH_TRACE

#include "crane_fn.h"
#include "obj.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

template <typename A> struct List;
enum class Comparison;
struct Positive;
struct Z;
struct Q;

struct Datatypes {
  static Comparison CompOpp(Comparison r);
};

struct QArith_base {
  static bool Qle_bool(const Q &x, const Q &y);
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
  Positive(Positive &&) = default;
  Positive &operator=(Positive &&) = default;

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
  static Positive mul(const Positive &x, Positive y);
  static Comparison compare_cont(Comparison r, const Positive &x,
                                 const Positive &y);
  static Comparison compare(const Positive &x0_, const Positive &x1_);
  static bool eqb(const Positive &p, const Positive &q);

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
};

struct BinInt {
  static Z double_(const Z &x);
  static Z succ_double(const Z &x);
  static Z pred_double(const Z &x);
  static Z pos_sub(const Positive &x, const Positive &y);
  static Z add(Z x, Z y);
  static Z opp(const Z &x);
  static Z sub(const Z &m, const Z &n);
  static Z mul(const Z &x, const Z &y);
  static Comparison compare(const Z &x, const Z &y);
  static bool leb(const Z &x, const Z &y);
  static bool ltb(const Z &x, const Z &y);
  static bool eqb(const Z &x, const Z &y);
  static uint64_t to_nat(const Z &z);
  static std::pair<Z, Z> pos_div_eucl(const Positive &a, const Z &b);
  static std::pair<Z, Z> div_eucl(const Z &a, const Z &b);
  static Z div(const Z &a, const Z &b);
  static Z modulo(const Z &a, const Z &b);
  static Z abs(const Z &z);
};

struct Q {
  Z Qnum;
  Positive Qden;
};

struct EpochCellGlyphTraceCase {
  enum class LunarPhase { NEWMOON, FIRSTQUARTER, FULLMOON, LASTQUARTER };

  template <typename T1>
  static T1 LunarPhase_rect(T1 f, T1 f0, T1 f1, T1 f2, LunarPhase l) {
    switch (l) {
    case LunarPhase::NEWMOON: {
      return f;
    }
    case LunarPhase::FIRSTQUARTER: {
      return f0;
    }
    case LunarPhase::FULLMOON: {
      return f1;
    }
    case LunarPhase::LASTQUARTER: {
      return f2;
    }
    default:
      std::unreachable();
    }
  }

  template <typename T1>
  static T1 LunarPhase_rec(T1 f, T1 f0, T1 f1, T1 f2, LunarPhase l) {
    switch (l) {
    case LunarPhase::NEWMOON: {
      return f;
    }
    case LunarPhase::FIRSTQUARTER: {
      return f0;
    }
    case LunarPhase::FULLMOON: {
      return f1;
    }
    case LunarPhase::LASTQUARTER: {
      return f2;
    }
    default:
      std::unreachable();
    }
  }

  static uint64_t phase_code(LunarPhase p);
  static LunarPhase phase_from_angle(const Z &angle_deg);
  enum class ZodiacSign {
    ARIES,
    TAURUS,
    GEMINI,
    CANCER,
    LEO,
    VIRGO,
    LIBRA,
    SCORPIO,
    SAGITTARIUS,
    CAPRICORN,
    AQUARIUS,
    PISCES
  };

  template <typename T1>
  static T1 ZodiacSign_rect(T1 f, T1 f0, T1 f1, T1 f2, T1 f3, T1 f4, T1 f5,
                            T1 f6, T1 f7, T1 f8, T1 f9, T1 f10, ZodiacSign z) {
    switch (z) {
    case ZodiacSign::ARIES: {
      return f;
    }
    case ZodiacSign::TAURUS: {
      return f0;
    }
    case ZodiacSign::GEMINI: {
      return f1;
    }
    case ZodiacSign::CANCER: {
      return f2;
    }
    case ZodiacSign::LEO: {
      return f3;
    }
    case ZodiacSign::VIRGO: {
      return f4;
    }
    case ZodiacSign::LIBRA: {
      return f5;
    }
    case ZodiacSign::SCORPIO: {
      return f6;
    }
    case ZodiacSign::SAGITTARIUS: {
      return f7;
    }
    case ZodiacSign::CAPRICORN: {
      return f8;
    }
    case ZodiacSign::AQUARIUS: {
      return f9;
    }
    case ZodiacSign::PISCES: {
      return f10;
    }
    default:
      std::unreachable();
    }
  }

  template <typename T1>
  static T1 ZodiacSign_rec(T1 f, T1 f0, T1 f1, T1 f2, T1 f3, T1 f4, T1 f5,
                           T1 f6, T1 f7, T1 f8, T1 f9, T1 f10, ZodiacSign z) {
    switch (z) {
    case ZodiacSign::ARIES: {
      return f;
    }
    case ZodiacSign::TAURUS: {
      return f0;
    }
    case ZodiacSign::GEMINI: {
      return f1;
    }
    case ZodiacSign::CANCER: {
      return f2;
    }
    case ZodiacSign::LEO: {
      return f3;
    }
    case ZodiacSign::VIRGO: {
      return f4;
    }
    case ZodiacSign::LIBRA: {
      return f5;
    }
    case ZodiacSign::SCORPIO: {
      return f6;
    }
    case ZodiacSign::SAGITTARIUS: {
      return f7;
    }
    case ZodiacSign::CAPRICORN: {
      return f8;
    }
    case ZodiacSign::AQUARIUS: {
      return f9;
    }
    case ZodiacSign::PISCES: {
      return f10;
    }
    default:
      std::unreachable();
    }
  }

  static uint64_t zodiac_code(ZodiacSign z);
  static bool eclipse_possible_at_dial(const Z &dial_pos);

  struct MechanismState {
    Z crank_position;
    Z metonic_dial;
    Z saros_dial;
    Z callippic_dial;
    Z exeligmos_dial;
    Z games_dial;
    Z zodiac_position;
  };

  static inline const MechanismState initial_state = MechanismState{
      Z::z0(), Z::z0(), Z::z0(), Z::z0(), Z::z0(), Z::z0(), Z::z0()};
  static inline const Z metonic_modulus =
      Z::zpos(Positive::xi(Positive::xi(Positive::xo(Positive::xi(
          Positive::xo(Positive::xi(Positive::xi(Positive::xh()))))))));
  static inline const Z saros_modulus =
      Z::zpos(Positive::xi(Positive::xi(Positive::xi(Positive::xi(
          Positive::xi(Positive::xo(Positive::xi(Positive::xh()))))))));
  static inline const Z callippic_modulus = Z::zpos(Positive::xo(Positive::xo(
      Positive::xi(Positive::xi(Positive::xo(Positive::xo(Positive::xh())))))));
  static inline const Z exeligmos_modulus =
      Z::zpos(Positive::xi(Positive::xh()));
  static inline const Z games_modulus =
      Z::zpos(Positive::xo(Positive::xo(Positive::xh())));
  static inline const Z zodiac_modulus =
      Z::zpos(Positive::xo(Positive::xo(Positive::xo(Positive::xi(Positive::xo(
          Positive::xi(Positive::xi(Positive::xo(Positive::xh())))))))));
  static MechanismState step(const MechanismState &s);
  static MechanismState step_reverse(const MechanismState &s);
  static MechanismState step_n(uint64_t n, MechanismState s);
  static MechanismState state_at_cell(const Z &cell);
  static LunarPhase predict_moon_phase_from_state(const MechanismState &s);
  static Z predict_olympiad_year(const MechanismState &s);
  static ZodiacSign predict_zodiac_sign(const MechanismState &s);
  enum class EclipseCategory {
    EC_TOTALLUNAR,
    EC_PARTIALLUNAR,
    EC_TOTALSOLAR,
    EC_ANNULARSOLAR,
    EC_PARTIALSOLAR
  };

  template <typename T1>
  static T1 EclipseCategory_rect(T1 f, T1 f0, T1 f1, T1 f2, T1 f3,
                                 EclipseCategory e) {
    switch (e) {
    case EclipseCategory::EC_TOTALLUNAR: {
      return f;
    }
    case EclipseCategory::EC_PARTIALLUNAR: {
      return f0;
    }
    case EclipseCategory::EC_TOTALSOLAR: {
      return f1;
    }
    case EclipseCategory::EC_ANNULARSOLAR: {
      return f2;
    }
    case EclipseCategory::EC_PARTIALSOLAR: {
      return f3;
    }
    default:
      std::unreachable();
    }
  }

  template <typename T1>
  static T1 EclipseCategory_rec(T1 f, T1 f0, T1 f1, T1 f2, T1 f3,
                                EclipseCategory e) {
    switch (e) {
    case EclipseCategory::EC_TOTALLUNAR: {
      return f;
    }
    case EclipseCategory::EC_PARTIALLUNAR: {
      return f0;
    }
    case EclipseCategory::EC_TOTALSOLAR: {
      return f1;
    }
    case EclipseCategory::EC_ANNULARSOLAR: {
      return f2;
    }
    case EclipseCategory::EC_PARTIALSOLAR: {
      return f3;
    }
    default:
      std::unreachable();
    }
  }

  static uint64_t eclipse_category_code(EclipseCategory c);

  struct HistoricalEclipse {
    Z he_year;
    Z he_month;
    Z he_day;
    EclipseCategory he_category;
    Z he_saros_series;
    Z he_saros_member;
    Q he_magnitude;
    bool he_visible_mediterranean;
  };
  enum class DialGlyph {
    GLYPH_SIGMA,
    GLYPH_ETA,
    GLYPH_SIGMATOTAL,
    GLYPH_ETAANNULAR,
    GLYPH_EMPTY
  };

  template <typename T1>
  static T1 DialGlyph_rect(T1 f, T1 f0, T1 f1, T1 f2, T1 f3, DialGlyph d) {
    switch (d) {
    case DialGlyph::GLYPH_SIGMA: {
      return f;
    }
    case DialGlyph::GLYPH_ETA: {
      return f0;
    }
    case DialGlyph::GLYPH_SIGMATOTAL: {
      return f1;
    }
    case DialGlyph::GLYPH_ETAANNULAR: {
      return f2;
    }
    case DialGlyph::GLYPH_EMPTY: {
      return f3;
    }
    default:
      std::unreachable();
    }
  }

  template <typename T1>
  static T1 DialGlyph_rec(T1 f, T1 f0, T1 f1, T1 f2, T1 f3, DialGlyph d) {
    switch (d) {
    case DialGlyph::GLYPH_SIGMA: {
      return f;
    }
    case DialGlyph::GLYPH_ETA: {
      return f0;
    }
    case DialGlyph::GLYPH_SIGMATOTAL: {
      return f1;
    }
    case DialGlyph::GLYPH_ETAANNULAR: {
      return f2;
    }
    case DialGlyph::GLYPH_EMPTY: {
      return f3;
    }
    default:
      std::unreachable();
    }
  }

  static uint64_t glyph_code(DialGlyph g);
  static bool category_matches_glyph(EclipseCategory cat, DialGlyph g);
  static DialGlyph glyph_at_cell(const Z &cell);
  static inline const HistoricalEclipse eclipse_may_205_bc = HistoricalEclipse{
      Z::zneg(Positive::xo(Positive::xo(Positive::xi(Positive::xi(
          Positive::xo(Positive::xo(Positive::xi(Positive::xh())))))))),
      Z::zpos(Positive::xi(Positive::xo(Positive::xh()))),
      Z::zpos(Positive::xo(Positive::xo(Positive::xi(Positive::xh())))),
      EclipseCategory::EC_TOTALLUNAR,
      Z::zpos(Positive::xo(Positive::xo(
          Positive::xi(Positive::xi(Positive::xo(Positive::xh())))))),
      Z::zpos(Positive::xo(Positive::xi(
          Positive::xo(Positive::xo(Positive::xo(Positive::xh())))))),
      Q{Z::zpos(Positive::xi(Positive::xo(Positive::xi(Positive::xo(
            Positive::xo(Positive::xi(Positive::xo(Positive::xh())))))))),
        Positive::xo(Positive::xo(Positive::xi(
            Positive::xo(Positive::xo(Positive::xi(Positive::xh()))))))},
      true};
  static inline const HistoricalEclipse eclipse_nov_205_bc = HistoricalEclipse{
      Z::zneg(Positive::xo(Positive::xo(Positive::xi(Positive::xi(
          Positive::xo(Positive::xo(Positive::xi(Positive::xh())))))))),
      Z::zpos(Positive::xi(Positive::xi(Positive::xo(Positive::xh())))),
      Z::zpos(Positive::xi(
          Positive::xi(Positive::xi(Positive::xo(Positive::xh()))))),
      EclipseCategory::EC_TOTALLUNAR,
      Z::zpos(Positive::xi(Positive::xo(
          Positive::xo(Positive::xo(Positive::xi(Positive::xh())))))),
      Z::zpos(Positive::xo(Positive::xo(
          Positive::xo(Positive::xo(Positive::xo(Positive::xh())))))),
      Q{Z::zpos(Positive::xo(Positive::xi(Positive::xi(Positive::xi(
            Positive::xo(Positive::xo(Positive::xo(Positive::xh())))))))),
        Positive::xo(Positive::xo(Positive::xi(
            Positive::xo(Positive::xo(Positive::xi(Positive::xh()))))))},
      true};
  static inline const HistoricalEclipse eclipse_may_204_bc = HistoricalEclipse{
      Z::zneg(Positive::xi(Positive::xi(Positive::xo(Positive::xi(
          Positive::xo(Positive::xo(Positive::xi(Positive::xh())))))))),
      Z::zpos(Positive::xi(Positive::xo(Positive::xh()))),
      Z::zpos(Positive::xh()),
      EclipseCategory::EC_PARTIALSOLAR,
      Z::zpos(Positive::xo(Positive::xo(
          Positive::xi(Positive::xi(Positive::xo(Positive::xh())))))),
      Z::zpos(Positive::xi(Positive::xi(
          Positive::xo(Positive::xo(Positive::xo(Positive::xh())))))),
      Q{Z::zpos(Positive::xo(Positive::xi(
            Positive::xo(Positive::xo(Positive::xo(Positive::xh())))))),
        Positive::xo(Positive::xo(Positive::xi(
            Positive::xo(Positive::xo(Positive::xi(Positive::xh()))))))},
      true};
  static inline const HistoricalEclipse eclipse_oct_204_bc = HistoricalEclipse{
      Z::zneg(Positive::xi(Positive::xi(Positive::xo(Positive::xi(
          Positive::xo(Positive::xo(Positive::xi(Positive::xh())))))))),
      Z::zpos(Positive::xo(Positive::xi(Positive::xo(Positive::xh())))),
      Z::zpos(Positive::xo(
          Positive::xi(Positive::xo(Positive::xi(Positive::xh()))))),
      EclipseCategory::EC_TOTALLUNAR,
      Z::zpos(Positive::xi(Positive::xi(
          Positive::xo(Positive::xi(Positive::xi(Positive::xh())))))),
      Z::zpos(Positive::xi(
          Positive::xi(Positive::xo(Positive::xi(Positive::xh()))))),
      Q{Z::zpos(Positive::xo(Positive::xo(Positive::xo(Positive::xi(
            Positive::xo(Positive::xo(Positive::xo(Positive::xh())))))))),
        Positive::xo(Positive::xo(Positive::xi(
            Positive::xo(Positive::xo(Positive::xi(Positive::xh()))))))},
      true};
  static inline const HistoricalEclipse eclipse_mar_187_bc = HistoricalEclipse{
      Z::zneg(Positive::xo(Positive::xi(Positive::xo(Positive::xi(
          Positive::xi(Positive::xi(Positive::xo(Positive::xh())))))))),
      Z::zpos(Positive::xi(Positive::xh())),
      Z::zpos(Positive::xo(Positive::xi(Positive::xi(Positive::xh())))),
      EclipseCategory::EC_TOTALLUNAR,
      Z::zpos(Positive::xo(Positive::xo(
          Positive::xi(Positive::xi(Positive::xo(Positive::xh())))))),
      Z::zpos(Positive::xi(Positive::xi(
          Positive::xo(Positive::xo(Positive::xo(Positive::xh())))))),
      Q{Z::zpos(Positive::xi(Positive::xo(Positive::xo(Positive::xo(
            Positive::xo(Positive::xi(Positive::xo(Positive::xh())))))))),
        Positive::xo(Positive::xo(Positive::xi(
            Positive::xo(Positive::xo(Positive::xi(Positive::xh()))))))},
      true};
  static inline const HistoricalEclipse eclipse_jun_178_bc = HistoricalEclipse{
      Z::zneg(Positive::xi(Positive::xo(Positive::xo(Positive::xo(
          Positive::xi(Positive::xi(Positive::xo(Positive::xh())))))))),
      Z::zpos(Positive::xo(Positive::xi(Positive::xh()))),
      Z::zpos(Positive::xi(
          Positive::xo(Positive::xi(Positive::xo(Positive::xh()))))),
      EclipseCategory::EC_TOTALLUNAR,
      Z::zpos(Positive::xo(Positive::xo(
          Positive::xo(Positive::xi(Positive::xi(Positive::xh())))))),
      Z::zpos(Positive::xo(Positive::xo(
          Positive::xi(Positive::xo(Positive::xo(Positive::xh())))))),
      Q{Z::zpos(Positive::xo(Positive::xo(Positive::xi(Positive::xi(
            Positive::xi(Positive::xo(Positive::xo(Positive::xh())))))))),
        Positive::xo(Positive::xo(Positive::xi(
            Positive::xo(Positive::xo(Positive::xi(Positive::xh()))))))},
      true};
  static inline const List<HistoricalEclipse> eclipse_database =
      List<HistoricalEclipse>::cons(
          eclipse_may_205_bc,
          List<HistoricalEclipse>::cons(
              eclipse_nov_205_bc,
              List<HistoricalEclipse>::cons(
                  eclipse_may_204_bc,
                  List<HistoricalEclipse>::cons(
                      eclipse_oct_204_bc,
                      List<HistoricalEclipse>::cons(
                          eclipse_mar_187_bc,
                          List<HistoricalEclipse>::cons(
                              eclipse_jun_178_bc,
                              List<HistoricalEclipse>::nil()))))));
  static uint64_t count_total_lunar(const List<HistoricalEclipse> &es);
  static uint64_t count_visible_total_lunar(const List<HistoricalEclipse> &es);
  static uint64_t visible_series_checksum(const List<HistoricalEclipse> &es);
  static Z months_from_epoch(const Z &epoch_year, const Z &eclipse_year,
                             const Z &epoch_month, const Z &eclipse_month);
  static Z saros_cell(const Z &epoch_year, const Z &epoch_month,
                      const HistoricalEclipse &e);
  static Z saros_dial_at_month(const Z &start_cell, const Z &months);

  struct EpochReading {
    MechanismState reading_state;
    HistoricalEclipse reading_eclipse;
    Z reading_cell;
    DialGlyph reading_glyph;
  };

  static EpochReading build_epoch_reading(const Z &epoch_year,
                                          const Z &epoch_month,
                                          const HistoricalEclipse &e);
  static bool reading_matches(const EpochReading &reading);
  static uint64_t reading_phase_code(const EpochReading &reading);
  static uint64_t reading_zodiac_code(const EpochReading &reading);

  struct ValidEpoch {
    Z ve_year;
    Z ve_month;
    HistoricalEclipse ve_eclipse;
  };

  static inline const ValidEpoch epoch_205_bc_valid = ValidEpoch{
      Z::zneg(Positive::xo(Positive::xo(Positive::xi(Positive::xi(
          Positive::xo(Positive::xo(Positive::xi(Positive::xh())))))))),
      Z::zpos(Positive::xi(Positive::xo(Positive::xh()))), eclipse_may_205_bc};
  static inline const EpochReading sample_epoch_reading = build_epoch_reading(
      epoch_205_bc_valid.ve_year, epoch_205_bc_valid.ve_month,
      epoch_205_bc_valid.ve_eclipse);
  static uint64_t phase_code_after_steps(uint64_t n);
  static uint64_t zodiac_code_after_steps(uint64_t n);
  static constexpr uint64_t sample_total_lunar_count = UINT64_C(5);
  static constexpr uint64_t sample_total_lunar_visible_count = UINT64_C(5);
  static constexpr uint64_t sample_visible_series_checksum = UINT64_C(296);
  static constexpr bool sample_epoch_cell_zero = true;
  static constexpr bool sample_epoch_glyph_match = true;
  static constexpr uint64_t sample_epoch_phase_code = UINT64_C(0);
  static constexpr uint64_t sample_epoch_zodiac_code = UINT64_C(0);
  static constexpr bool sample_valid_epoch_visible = true;
  static constexpr bool sample_valid_epoch_series_44 = true;
  static constexpr bool sample_valid_epoch_magnitude_ge_one = true;
  static constexpr bool sample_step_roundtrip_saros = true;
  static constexpr bool sample_olympiad_year_is_one_after_4 = true;
  static constexpr bool sample_eclipse_possible_after_6 = true;
  static inline const bool sample_epoch_178_misaligned = !(BinInt::eqb(
      saros_cell(
          Z::zneg(Positive::xo(Positive::xo(Positive::xi(Positive::xi(
              Positive::xo(Positive::xo(Positive::xi(Positive::xh())))))))),
          Z::zpos(Positive::xi(Positive::xo(Positive::xh()))),
          eclipse_jun_178_bc),
      Z::z0()));
};

#endif // INCLUDED_EPOCH_CELL_GLYPH_TRACE
