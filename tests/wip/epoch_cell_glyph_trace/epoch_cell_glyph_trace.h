#ifndef INCLUDED_EPOCH_CELL_GLYPH_TRACE
#define INCLUDED_EPOCH_CELL_GLYPH_TRACE

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

template <typename t_A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    t_A d_a0;
    std::shared_ptr<List<t_A>> d_a1;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t d_v_;

  // CREATORS
  explicit List(Nil _v) : d_v_(std::move(_v)) {}

  explicit List(Cons _v) : d_v_(std::move(_v)) {}

public:
  // TYPES
  struct ctor {
    ctor() = delete;

    static std::shared_ptr<List<t_A>> Nil_() {
      return std::shared_ptr<List<t_A>>(new List<t_A>(Nil{}));
    }

    static std::shared_ptr<List<t_A>>
    Cons_(t_A a0, const std::shared_ptr<List<t_A>> &a1) {
      return std::shared_ptr<List<t_A>>(new List<t_A>(Cons{a0, a1}));
    }

    static std::unique_ptr<List<t_A>> Nil_uptr() {
      return std::unique_ptr<List<t_A>>(new List<t_A>(Nil{}));
    }

    static std::unique_ptr<List<t_A>>
    Cons_uptr(t_A a0, const std::shared_ptr<List<t_A>> &a1) {
      return std::unique_ptr<List<t_A>>(new List<t_A>(Cons{a0, a1}));
    }
  };

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
};
enum class Comparison { e_EQ, e_LT, e_GT };

struct Positive {
  // TYPES
  struct XI {
    std::shared_ptr<Positive> d_a0;
  };

  struct XO {
    std::shared_ptr<Positive> d_a0;
  };

  struct XH {};

  using variant_t = std::variant<XI, XO, XH>;

private:
  // DATA
  variant_t d_v_;

  // CREATORS
  explicit Positive(XI _v) : d_v_(std::move(_v)) {}

  explicit Positive(XO _v) : d_v_(std::move(_v)) {}

  explicit Positive(XH _v) : d_v_(std::move(_v)) {}

public:
  // TYPES
  struct ctor {
    ctor() = delete;

    static std::shared_ptr<Positive> XI_(const std::shared_ptr<Positive> &a0) {
      return std::shared_ptr<Positive>(new Positive(XI{a0}));
    }

    static std::shared_ptr<Positive> XO_(const std::shared_ptr<Positive> &a0) {
      return std::shared_ptr<Positive>(new Positive(XO{a0}));
    }

    static std::shared_ptr<Positive> XH_() {
      return std::shared_ptr<Positive>(new Positive(XH{}));
    }

    static std::unique_ptr<Positive>
    XI_uptr(const std::shared_ptr<Positive> &a0) {
      return std::unique_ptr<Positive>(new Positive(XI{a0}));
    }

    static std::unique_ptr<Positive>
    XO_uptr(const std::shared_ptr<Positive> &a0) {
      return std::unique_ptr<Positive>(new Positive(XO{a0}));
    }

    static std::unique_ptr<Positive> XH_uptr() {
      return std::unique_ptr<Positive>(new Positive(XH{}));
    }
  };

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
};

struct Z {
  // TYPES
  struct Z0 {};

  struct Zpos {
    std::shared_ptr<Positive> d_a0;
  };

  struct Zneg {
    std::shared_ptr<Positive> d_a0;
  };

  using variant_t = std::variant<Z0, Zpos, Zneg>;

private:
  // DATA
  variant_t d_v_;

  // CREATORS
  explicit Z(Z0 _v) : d_v_(std::move(_v)) {}

  explicit Z(Zpos _v) : d_v_(std::move(_v)) {}

  explicit Z(Zneg _v) : d_v_(std::move(_v)) {}

public:
  // TYPES
  struct ctor {
    ctor() = delete;

    static std::shared_ptr<Z> Z0_() { return std::shared_ptr<Z>(new Z(Z0{})); }

    static std::shared_ptr<Z> Zpos_(const std::shared_ptr<Positive> &a0) {
      return std::shared_ptr<Z>(new Z(Zpos{a0}));
    }

    static std::shared_ptr<Z> Zneg_(const std::shared_ptr<Positive> &a0) {
      return std::shared_ptr<Z>(new Z(Zneg{a0}));
    }

    static std::unique_ptr<Z> Z0_uptr() {
      return std::unique_ptr<Z>(new Z(Z0{}));
    }

    static std::unique_ptr<Z> Zpos_uptr(const std::shared_ptr<Positive> &a0) {
      return std::unique_ptr<Z>(new Z(Zpos{a0}));
    }

    static std::unique_ptr<Z> Zneg_uptr(const std::shared_ptr<Positive> &a0) {
      return std::unique_ptr<Z>(new Z(Zneg{a0}));
    }
  };

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
};

struct Pos {
  static std::shared_ptr<Positive> succ(const std::shared_ptr<Positive> &x);
  static std::shared_ptr<Positive> add(const std::shared_ptr<Positive> &x,
                                       const std::shared_ptr<Positive> &y);
  static std::shared_ptr<Positive>
  add_carry(const std::shared_ptr<Positive> &x,
            const std::shared_ptr<Positive> &y);
  static std::shared_ptr<Positive>
  pred_double(const std::shared_ptr<Positive> &x);
  static std::shared_ptr<Positive> mul(const std::shared_ptr<Positive> &x,
                                       std::shared_ptr<Positive> y);
  __attribute__((pure)) static Comparison
  compare_cont(const Comparison r, const std::shared_ptr<Positive> &x,
               const std::shared_ptr<Positive> &y);
  __attribute__((pure)) static Comparison
  compare(const std::shared_ptr<Positive> &_x0,
          const std::shared_ptr<Positive> &_x1);
  __attribute__((pure)) static bool eqb(const std::shared_ptr<Positive> &p,
                                        const std::shared_ptr<Positive> &q);

  template <typename T1, MapsTo<T1, T1, T1> F0>
  static T1 iter_op(F0 &&op, const std::shared_ptr<Positive> &p, const T1 a) {
    return std::visit(
        Overloaded{[&](const typename Positive::XI _args) -> T1 {
                     return op(a, iter_op<T1>(op, _args.d_a0, op(a, a)));
                   },
                   [&](const typename Positive::XO _args) -> T1 {
                     return iter_op<T1>(op, _args.d_a0, op(a, a));
                   },
                   [&](const typename Positive::XH _args) -> T1 { return a; }},
        p->v());
  }

  __attribute__((pure)) static unsigned int
  to_nat(const std::shared_ptr<Positive> &x);
};

struct BinInt {
  static std::shared_ptr<Z> double_(const std::shared_ptr<Z> &x);
  static std::shared_ptr<Z> succ_double(const std::shared_ptr<Z> &x);
  static std::shared_ptr<Z> pred_double(const std::shared_ptr<Z> &x);
  static std::shared_ptr<Z> pos_sub(const std::shared_ptr<Positive> &x,
                                    const std::shared_ptr<Positive> &y);
  static std::shared_ptr<Z> add(std::shared_ptr<Z> x, std::shared_ptr<Z> y);
  static std::shared_ptr<Z> opp(const std::shared_ptr<Z> &x);
  static std::shared_ptr<Z> sub(const std::shared_ptr<Z> &m,
                                const std::shared_ptr<Z> &n);
  static std::shared_ptr<Z> mul(const std::shared_ptr<Z> &x,
                                const std::shared_ptr<Z> &y);
  __attribute__((pure)) static Comparison compare(const std::shared_ptr<Z> &x,
                                                  const std::shared_ptr<Z> &y);
  __attribute__((pure)) static bool leb(const std::shared_ptr<Z> &x,
                                        const std::shared_ptr<Z> &y);
  __attribute__((pure)) static bool ltb(const std::shared_ptr<Z> &x,
                                        const std::shared_ptr<Z> &y);
  __attribute__((pure)) static bool eqb(const std::shared_ptr<Z> &x,
                                        const std::shared_ptr<Z> &y);
  __attribute__((pure)) static unsigned int to_nat(const std::shared_ptr<Z> &z);
  __attribute__((pure)) static std::pair<std::shared_ptr<Z>, std::shared_ptr<Z>>
  pos_div_eucl(const std::shared_ptr<Positive> &a, std::shared_ptr<Z> b);
  __attribute__((pure)) static std::pair<std::shared_ptr<Z>, std::shared_ptr<Z>>
  div_eucl(std::shared_ptr<Z> a, std::shared_ptr<Z> b);
  static std::shared_ptr<Z> div(const std::shared_ptr<Z> &a,
                                const std::shared_ptr<Z> &b);
  static std::shared_ptr<Z> modulo(const std::shared_ptr<Z> &a,
                                   const std::shared_ptr<Z> &b);
  static std::shared_ptr<Z> abs(const std::shared_ptr<Z> &z);
};

struct Q {
  std::shared_ptr<Z> Qnum;
  std::shared_ptr<Positive> Qden;
};

struct Datatypes {
  __attribute__((pure)) static Comparison CompOpp(const Comparison r);
};

struct EpochCellGlyphTraceCase {
  enum class LunarPhase {
    e_NEWMOON,
    e_FIRSTQUARTER,
    e_FULLMOON,
    e_LASTQUARTER
  };

  template <typename T1>
  static T1 LunarPhase_rect(const T1 f, const T1 f0, const T1 f1, const T1 f2,
                            const LunarPhase l) {
    return [&](void) {
      switch (l) {
      case LunarPhase::e_NEWMOON: {
        return f;
      }
      case LunarPhase::e_FIRSTQUARTER: {
        return f0;
      }
      case LunarPhase::e_FULLMOON: {
        return f1;
      }
      case LunarPhase::e_LASTQUARTER: {
        return f2;
      }
      }
    }();
  }

  template <typename T1>
  static T1 LunarPhase_rec(const T1 f, const T1 f0, const T1 f1, const T1 f2,
                           const LunarPhase l) {
    return [&](void) {
      switch (l) {
      case LunarPhase::e_NEWMOON: {
        return f;
      }
      case LunarPhase::e_FIRSTQUARTER: {
        return f0;
      }
      case LunarPhase::e_FULLMOON: {
        return f1;
      }
      case LunarPhase::e_LASTQUARTER: {
        return f2;
      }
      }
    }();
  }

  __attribute__((pure)) static unsigned int phase_code(const LunarPhase p);
  __attribute__((pure)) static LunarPhase
  phase_from_angle(const std::shared_ptr<Z> &angle_deg);
  enum class ZodiacSign {
    e_ARIES,
    e_TAURUS,
    e_GEMINI,
    e_CANCER,
    e_LEO,
    e_VIRGO,
    e_LIBRA,
    e_SCORPIO,
    e_SAGITTARIUS,
    e_CAPRICORN,
    e_AQUARIUS,
    e_PISCES
  };

  template <typename T1>
  static T1 ZodiacSign_rect(const T1 f, const T1 f0, const T1 f1, const T1 f2,
                            const T1 f3, const T1 f4, const T1 f5, const T1 f6,
                            const T1 f7, const T1 f8, const T1 f9, const T1 f10,
                            const ZodiacSign z) {
    return [&](void) {
      switch (z) {
      case ZodiacSign::e_ARIES: {
        return f;
      }
      case ZodiacSign::e_TAURUS: {
        return f0;
      }
      case ZodiacSign::e_GEMINI: {
        return f1;
      }
      case ZodiacSign::e_CANCER: {
        return f2;
      }
      case ZodiacSign::e_LEO: {
        return f3;
      }
      case ZodiacSign::e_VIRGO: {
        return f4;
      }
      case ZodiacSign::e_LIBRA: {
        return f5;
      }
      case ZodiacSign::e_SCORPIO: {
        return f6;
      }
      case ZodiacSign::e_SAGITTARIUS: {
        return f7;
      }
      case ZodiacSign::e_CAPRICORN: {
        return f8;
      }
      case ZodiacSign::e_AQUARIUS: {
        return f9;
      }
      case ZodiacSign::e_PISCES: {
        return f10;
      }
      }
    }();
  }

  template <typename T1>
  static T1 ZodiacSign_rec(const T1 f, const T1 f0, const T1 f1, const T1 f2,
                           const T1 f3, const T1 f4, const T1 f5, const T1 f6,
                           const T1 f7, const T1 f8, const T1 f9, const T1 f10,
                           const ZodiacSign z) {
    return [&](void) {
      switch (z) {
      case ZodiacSign::e_ARIES: {
        return f;
      }
      case ZodiacSign::e_TAURUS: {
        return f0;
      }
      case ZodiacSign::e_GEMINI: {
        return f1;
      }
      case ZodiacSign::e_CANCER: {
        return f2;
      }
      case ZodiacSign::e_LEO: {
        return f3;
      }
      case ZodiacSign::e_VIRGO: {
        return f4;
      }
      case ZodiacSign::e_LIBRA: {
        return f5;
      }
      case ZodiacSign::e_SCORPIO: {
        return f6;
      }
      case ZodiacSign::e_SAGITTARIUS: {
        return f7;
      }
      case ZodiacSign::e_CAPRICORN: {
        return f8;
      }
      case ZodiacSign::e_AQUARIUS: {
        return f9;
      }
      case ZodiacSign::e_PISCES: {
        return f10;
      }
      }
    }();
  }

  __attribute__((pure)) static unsigned int zodiac_code(const ZodiacSign z);
  __attribute__((pure)) static bool
  eclipse_possible_at_dial(const std::shared_ptr<Z> &dial_pos);

  struct MechanismState {
    std::shared_ptr<Z> crank_position;
    std::shared_ptr<Z> metonic_dial;
    std::shared_ptr<Z> saros_dial;
    std::shared_ptr<Z> callippic_dial;
    std::shared_ptr<Z> exeligmos_dial;
    std::shared_ptr<Z> games_dial;
    std::shared_ptr<Z> zodiac_position;
  };

  static inline const std::shared_ptr<MechanismState> initial_state =
      std::make_shared<MechanismState>(MechanismState{
          Z::ctor::Z0_(), Z::ctor::Z0_(), Z::ctor::Z0_(), Z::ctor::Z0_(),
          Z::ctor::Z0_(), Z::ctor::Z0_(), Z::ctor::Z0_()});
  static inline const std::shared_ptr<Z> metonic_modulus = Z::ctor::Zpos_(
      Positive::ctor::XI_(Positive::ctor::XI_(Positive::ctor::XO_(
          Positive::ctor::XI_(Positive::ctor::XO_(Positive::ctor::XI_(
              Positive::ctor::XI_(Positive::ctor::XH_()))))))));
  static inline const std::shared_ptr<Z> saros_modulus = Z::ctor::Zpos_(
      Positive::ctor::XI_(Positive::ctor::XI_(Positive::ctor::XI_(
          Positive::ctor::XI_(Positive::ctor::XI_(Positive::ctor::XO_(
              Positive::ctor::XI_(Positive::ctor::XH_()))))))));
  static inline const std::shared_ptr<Z> callippic_modulus =
      Z::ctor::Zpos_(Positive::ctor::XO_(Positive::ctor::XO_(
          Positive::ctor::XI_(Positive::ctor::XI_(Positive::ctor::XO_(
              Positive::ctor::XO_(Positive::ctor::XH_())))))));
  static inline const std::shared_ptr<Z> exeligmos_modulus =
      Z::ctor::Zpos_(Positive::ctor::XI_(Positive::ctor::XH_()));
  static inline const std::shared_ptr<Z> games_modulus = Z::ctor::Zpos_(
      Positive::ctor::XO_(Positive::ctor::XO_(Positive::ctor::XH_())));
  static inline const std::shared_ptr<Z> zodiac_modulus =
      Z::ctor::Zpos_(Positive::ctor::XO_(
          Positive::ctor::XO_(Positive::ctor::XO_(Positive::ctor::XI_(
              Positive::ctor::XO_(Positive::ctor::XI_(Positive::ctor::XI_(
                  Positive::ctor::XO_(Positive::ctor::XH_())))))))));
  static std::shared_ptr<MechanismState>
  step(std::shared_ptr<MechanismState> s);
  static std::shared_ptr<MechanismState>
  step_reverse(std::shared_ptr<MechanismState> s);
  static std::shared_ptr<MechanismState>
  step_n(const unsigned int n, std::shared_ptr<MechanismState> s);
  static std::shared_ptr<MechanismState> state_at_cell(std::shared_ptr<Z> cell);
  __attribute__((pure)) static LunarPhase
  predict_moon_phase_from_state(const std::shared_ptr<MechanismState> &s);
  static std::shared_ptr<Z>
  predict_olympiad_year(const std::shared_ptr<MechanismState> &s);
  __attribute__((pure)) static ZodiacSign
  predict_zodiac_sign(const std::shared_ptr<MechanismState> &s);
  enum class EclipseCategory {
    e_EC_TOTALLUNAR,
    e_EC_PARTIALLUNAR,
    e_EC_TOTALSOLAR,
    e_EC_ANNULARSOLAR,
    e_EC_PARTIALSOLAR
  };

  template <typename T1>
  static T1 EclipseCategory_rect(const T1 f, const T1 f0, const T1 f1,
                                 const T1 f2, const T1 f3,
                                 const EclipseCategory e) {
    return [&](void) {
      switch (e) {
      case EclipseCategory::e_EC_TOTALLUNAR: {
        return f;
      }
      case EclipseCategory::e_EC_PARTIALLUNAR: {
        return f0;
      }
      case EclipseCategory::e_EC_TOTALSOLAR: {
        return f1;
      }
      case EclipseCategory::e_EC_ANNULARSOLAR: {
        return f2;
      }
      case EclipseCategory::e_EC_PARTIALSOLAR: {
        return f3;
      }
      }
    }();
  }

  template <typename T1>
  static T1 EclipseCategory_rec(const T1 f, const T1 f0, const T1 f1,
                                const T1 f2, const T1 f3,
                                const EclipseCategory e) {
    return [&](void) {
      switch (e) {
      case EclipseCategory::e_EC_TOTALLUNAR: {
        return f;
      }
      case EclipseCategory::e_EC_PARTIALLUNAR: {
        return f0;
      }
      case EclipseCategory::e_EC_TOTALSOLAR: {
        return f1;
      }
      case EclipseCategory::e_EC_ANNULARSOLAR: {
        return f2;
      }
      case EclipseCategory::e_EC_PARTIALSOLAR: {
        return f3;
      }
      }
    }();
  }

  __attribute__((pure)) static unsigned int
  eclipse_category_code(const EclipseCategory c);

  struct HistoricalEclipse {
    std::shared_ptr<Z> he_year;
    std::shared_ptr<Z> he_month;
    std::shared_ptr<Z> he_day;
    EclipseCategory he_category;
    std::shared_ptr<Z> he_saros_series;
    std::shared_ptr<Z> he_saros_member;
    std::shared_ptr<Q> he_magnitude;
    bool he_visible_mediterranean;
  };
  enum class DialGlyph {
    e_GLYPH_SIGMA,
    e_GLYPH_ETA,
    e_GLYPH_SIGMATOTAL,
    e_GLYPH_ETAANNULAR,
    e_GLYPH_EMPTY
  };

  template <typename T1>
  static T1 DialGlyph_rect(const T1 f, const T1 f0, const T1 f1, const T1 f2,
                           const T1 f3, const DialGlyph d) {
    return [&](void) {
      switch (d) {
      case DialGlyph::e_GLYPH_SIGMA: {
        return f;
      }
      case DialGlyph::e_GLYPH_ETA: {
        return f0;
      }
      case DialGlyph::e_GLYPH_SIGMATOTAL: {
        return f1;
      }
      case DialGlyph::e_GLYPH_ETAANNULAR: {
        return f2;
      }
      case DialGlyph::e_GLYPH_EMPTY: {
        return f3;
      }
      }
    }();
  }

  template <typename T1>
  static T1 DialGlyph_rec(const T1 f, const T1 f0, const T1 f1, const T1 f2,
                          const T1 f3, const DialGlyph d) {
    return [&](void) {
      switch (d) {
      case DialGlyph::e_GLYPH_SIGMA: {
        return f;
      }
      case DialGlyph::e_GLYPH_ETA: {
        return f0;
      }
      case DialGlyph::e_GLYPH_SIGMATOTAL: {
        return f1;
      }
      case DialGlyph::e_GLYPH_ETAANNULAR: {
        return f2;
      }
      case DialGlyph::e_GLYPH_EMPTY: {
        return f3;
      }
      }
    }();
  }

  __attribute__((pure)) static unsigned int glyph_code(const DialGlyph g);
  __attribute__((pure)) static bool
  category_matches_glyph(const EclipseCategory cat, const DialGlyph g);
  __attribute__((pure)) static DialGlyph
  glyph_at_cell(const std::shared_ptr<Z> &cell);
  static inline const std::shared_ptr<HistoricalEclipse> eclipse_may_205_bc =
      std::make_shared<HistoricalEclipse>(HistoricalEclipse{
          Z::ctor::Zneg_(
              Positive::ctor::XO_(Positive::ctor::XO_(Positive::ctor::XI_(
                  Positive::ctor::XI_(Positive::ctor::XO_(Positive::ctor::XO_(
                      Positive::ctor::XI_(Positive::ctor::XH_())))))))),
          Z::ctor::Zpos_(
              Positive::ctor::XI_(Positive::ctor::XO_(Positive::ctor::XH_()))),
          Z::ctor::Zpos_(Positive::ctor::XO_(
              Positive::ctor::XO_(Positive::ctor::XI_(Positive::ctor::XH_())))),
          EclipseCategory::e_EC_TOTALLUNAR,
          Z::ctor::Zpos_(Positive::ctor::XO_(
              Positive::ctor::XO_(Positive::ctor::XI_(Positive::ctor::XI_(
                  Positive::ctor::XO_(Positive::ctor::XH_())))))),
          Z::ctor::Zpos_(Positive::ctor::XO_(
              Positive::ctor::XI_(Positive::ctor::XO_(Positive::ctor::XO_(
                  Positive::ctor::XO_(Positive::ctor::XH_())))))),
          std::make_shared<Q>(
              Q{Z::ctor::Zpos_(Positive::ctor::XI_(
                    Positive::ctor::XO_(Positive::ctor::XI_(Positive::ctor::XO_(
                        Positive::ctor::XO_(Positive::ctor::XI_(
                            Positive::ctor::XO_(Positive::ctor::XH_())))))))),
                Positive::ctor::XO_(Positive::ctor::XO_(
                    Positive::ctor::XI_(Positive::ctor::XO_(Positive::ctor::XO_(
                        Positive::ctor::XI_(Positive::ctor::XH_()))))))}),
          true});
  static inline const std::shared_ptr<HistoricalEclipse> eclipse_nov_205_bc =
      std::make_shared<HistoricalEclipse>(HistoricalEclipse{
          Z::ctor::Zneg_(
              Positive::ctor::XO_(Positive::ctor::XO_(Positive::ctor::XI_(
                  Positive::ctor::XI_(Positive::ctor::XO_(Positive::ctor::XO_(
                      Positive::ctor::XI_(Positive::ctor::XH_())))))))),
          Z::ctor::Zpos_(Positive::ctor::XI_(
              Positive::ctor::XI_(Positive::ctor::XO_(Positive::ctor::XH_())))),
          Z::ctor::Zpos_(
              Positive::ctor::XI_(Positive::ctor::XI_(Positive::ctor::XI_(
                  Positive::ctor::XO_(Positive::ctor::XH_()))))),
          EclipseCategory::e_EC_TOTALLUNAR,
          Z::ctor::Zpos_(Positive::ctor::XI_(
              Positive::ctor::XO_(Positive::ctor::XO_(Positive::ctor::XO_(
                  Positive::ctor::XI_(Positive::ctor::XH_())))))),
          Z::ctor::Zpos_(Positive::ctor::XO_(
              Positive::ctor::XO_(Positive::ctor::XO_(Positive::ctor::XO_(
                  Positive::ctor::XO_(Positive::ctor::XH_())))))),
          std::make_shared<Q>(
              Q{Z::ctor::Zpos_(Positive::ctor::XO_(
                    Positive::ctor::XI_(Positive::ctor::XI_(Positive::ctor::XI_(
                        Positive::ctor::XO_(Positive::ctor::XO_(
                            Positive::ctor::XO_(Positive::ctor::XH_())))))))),
                Positive::ctor::XO_(Positive::ctor::XO_(
                    Positive::ctor::XI_(Positive::ctor::XO_(Positive::ctor::XO_(
                        Positive::ctor::XI_(Positive::ctor::XH_()))))))}),
          true});
  static inline const std::shared_ptr<HistoricalEclipse> eclipse_may_204_bc =
      std::make_shared<HistoricalEclipse>(HistoricalEclipse{
          Z::ctor::Zneg_(
              Positive::ctor::XI_(Positive::ctor::XI_(Positive::ctor::XO_(
                  Positive::ctor::XI_(Positive::ctor::XO_(Positive::ctor::XO_(
                      Positive::ctor::XI_(Positive::ctor::XH_())))))))),
          Z::ctor::Zpos_(
              Positive::ctor::XI_(Positive::ctor::XO_(Positive::ctor::XH_()))),
          Z::ctor::Zpos_(Positive::ctor::XH_()),
          EclipseCategory::e_EC_PARTIALSOLAR,
          Z::ctor::Zpos_(Positive::ctor::XO_(
              Positive::ctor::XO_(Positive::ctor::XI_(Positive::ctor::XI_(
                  Positive::ctor::XO_(Positive::ctor::XH_())))))),
          Z::ctor::Zpos_(Positive::ctor::XI_(
              Positive::ctor::XI_(Positive::ctor::XO_(Positive::ctor::XO_(
                  Positive::ctor::XO_(Positive::ctor::XH_())))))),
          std::make_shared<Q>(
              Q{Z::ctor::Zpos_(Positive::ctor::XO_(
                    Positive::ctor::XI_(Positive::ctor::XO_(Positive::ctor::XO_(
                        Positive::ctor::XO_(Positive::ctor::XH_())))))),
                Positive::ctor::XO_(Positive::ctor::XO_(
                    Positive::ctor::XI_(Positive::ctor::XO_(Positive::ctor::XO_(
                        Positive::ctor::XI_(Positive::ctor::XH_()))))))}),
          true});
  static inline const std::shared_ptr<HistoricalEclipse> eclipse_oct_204_bc =
      std::make_shared<HistoricalEclipse>(HistoricalEclipse{
          Z::ctor::Zneg_(
              Positive::ctor::XI_(Positive::ctor::XI_(Positive::ctor::XO_(
                  Positive::ctor::XI_(Positive::ctor::XO_(Positive::ctor::XO_(
                      Positive::ctor::XI_(Positive::ctor::XH_())))))))),
          Z::ctor::Zpos_(Positive::ctor::XO_(
              Positive::ctor::XI_(Positive::ctor::XO_(Positive::ctor::XH_())))),
          Z::ctor::Zpos_(
              Positive::ctor::XO_(Positive::ctor::XI_(Positive::ctor::XO_(
                  Positive::ctor::XI_(Positive::ctor::XH_()))))),
          EclipseCategory::e_EC_TOTALLUNAR,
          Z::ctor::Zpos_(Positive::ctor::XI_(
              Positive::ctor::XI_(Positive::ctor::XO_(Positive::ctor::XI_(
                  Positive::ctor::XI_(Positive::ctor::XH_())))))),
          Z::ctor::Zpos_(
              Positive::ctor::XI_(Positive::ctor::XI_(Positive::ctor::XO_(
                  Positive::ctor::XI_(Positive::ctor::XH_()))))),
          std::make_shared<Q>(
              Q{Z::ctor::Zpos_(Positive::ctor::XO_(
                    Positive::ctor::XO_(Positive::ctor::XO_(Positive::ctor::XI_(
                        Positive::ctor::XO_(Positive::ctor::XO_(
                            Positive::ctor::XO_(Positive::ctor::XH_())))))))),
                Positive::ctor::XO_(Positive::ctor::XO_(
                    Positive::ctor::XI_(Positive::ctor::XO_(Positive::ctor::XO_(
                        Positive::ctor::XI_(Positive::ctor::XH_()))))))}),
          true});
  static inline const std::shared_ptr<HistoricalEclipse> eclipse_mar_187_bc =
      std::make_shared<HistoricalEclipse>(HistoricalEclipse{
          Z::ctor::Zneg_(
              Positive::ctor::XO_(Positive::ctor::XI_(Positive::ctor::XO_(
                  Positive::ctor::XI_(Positive::ctor::XI_(Positive::ctor::XI_(
                      Positive::ctor::XO_(Positive::ctor::XH_())))))))),
          Z::ctor::Zpos_(Positive::ctor::XI_(Positive::ctor::XH_())),
          Z::ctor::Zpos_(Positive::ctor::XO_(
              Positive::ctor::XI_(Positive::ctor::XI_(Positive::ctor::XH_())))),
          EclipseCategory::e_EC_TOTALLUNAR,
          Z::ctor::Zpos_(Positive::ctor::XO_(
              Positive::ctor::XO_(Positive::ctor::XI_(Positive::ctor::XI_(
                  Positive::ctor::XO_(Positive::ctor::XH_())))))),
          Z::ctor::Zpos_(Positive::ctor::XI_(
              Positive::ctor::XI_(Positive::ctor::XO_(Positive::ctor::XO_(
                  Positive::ctor::XO_(Positive::ctor::XH_())))))),
          std::make_shared<Q>(
              Q{Z::ctor::Zpos_(Positive::ctor::XI_(
                    Positive::ctor::XO_(Positive::ctor::XO_(Positive::ctor::XO_(
                        Positive::ctor::XO_(Positive::ctor::XI_(
                            Positive::ctor::XO_(Positive::ctor::XH_())))))))),
                Positive::ctor::XO_(Positive::ctor::XO_(
                    Positive::ctor::XI_(Positive::ctor::XO_(Positive::ctor::XO_(
                        Positive::ctor::XI_(Positive::ctor::XH_()))))))}),
          true});
  static inline const std::shared_ptr<HistoricalEclipse> eclipse_jun_178_bc =
      std::make_shared<HistoricalEclipse>(HistoricalEclipse{
          Z::ctor::Zneg_(
              Positive::ctor::XI_(Positive::ctor::XO_(Positive::ctor::XO_(
                  Positive::ctor::XO_(Positive::ctor::XI_(Positive::ctor::XI_(
                      Positive::ctor::XO_(Positive::ctor::XH_())))))))),
          Z::ctor::Zpos_(
              Positive::ctor::XO_(Positive::ctor::XI_(Positive::ctor::XH_()))),
          Z::ctor::Zpos_(
              Positive::ctor::XI_(Positive::ctor::XO_(Positive::ctor::XI_(
                  Positive::ctor::XO_(Positive::ctor::XH_()))))),
          EclipseCategory::e_EC_TOTALLUNAR,
          Z::ctor::Zpos_(Positive::ctor::XO_(
              Positive::ctor::XO_(Positive::ctor::XO_(Positive::ctor::XI_(
                  Positive::ctor::XI_(Positive::ctor::XH_())))))),
          Z::ctor::Zpos_(Positive::ctor::XO_(
              Positive::ctor::XO_(Positive::ctor::XI_(Positive::ctor::XO_(
                  Positive::ctor::XO_(Positive::ctor::XH_())))))),
          std::make_shared<Q>(
              Q{Z::ctor::Zpos_(Positive::ctor::XO_(
                    Positive::ctor::XO_(Positive::ctor::XI_(Positive::ctor::XI_(
                        Positive::ctor::XI_(Positive::ctor::XO_(
                            Positive::ctor::XO_(Positive::ctor::XH_())))))))),
                Positive::ctor::XO_(Positive::ctor::XO_(
                    Positive::ctor::XI_(Positive::ctor::XO_(Positive::ctor::XO_(
                        Positive::ctor::XI_(Positive::ctor::XH_()))))))}),
          true});
  static inline const std::shared_ptr<List<std::shared_ptr<HistoricalEclipse>>>
      eclipse_database = List<std::shared_ptr<HistoricalEclipse>>::ctor::Cons_(
          eclipse_may_205_bc,
          List<std::shared_ptr<HistoricalEclipse>>::ctor::Cons_(
              eclipse_nov_205_bc,
              List<std::shared_ptr<HistoricalEclipse>>::ctor::Cons_(
                  eclipse_may_204_bc,
                  List<std::shared_ptr<HistoricalEclipse>>::ctor::Cons_(
                      eclipse_oct_204_bc,
                      List<std::shared_ptr<HistoricalEclipse>>::ctor::Cons_(
                          eclipse_mar_187_bc,
                          List<std::shared_ptr<HistoricalEclipse>>::ctor::Cons_(
                              eclipse_jun_178_bc,
                              List<std::shared_ptr<HistoricalEclipse>>::ctor::
                                  Nil_()))))));
  __attribute__((pure)) static unsigned int count_total_lunar(
      const std::shared_ptr<List<std::shared_ptr<HistoricalEclipse>>> &es);
  __attribute__((pure)) static unsigned int count_visible_total_lunar(
      const std::shared_ptr<List<std::shared_ptr<HistoricalEclipse>>> &es);
  __attribute__((pure)) static unsigned int visible_series_checksum(
      const std::shared_ptr<List<std::shared_ptr<HistoricalEclipse>>> &es);
  static std::shared_ptr<Z>
  months_from_epoch(const std::shared_ptr<Z> &epoch_year,
                    const std::shared_ptr<Z> &eclipse_year,
                    const std::shared_ptr<Z> &epoch_month,
                    const std::shared_ptr<Z> &eclipse_month);
  static std::shared_ptr<Z>
  saros_cell(const std::shared_ptr<Z> &epoch_year,
             const std::shared_ptr<Z> &epoch_month,
             const std::shared_ptr<HistoricalEclipse> &e);
  static std::shared_ptr<Z>
  saros_dial_at_month(const std::shared_ptr<Z> &start_cell,
                      const std::shared_ptr<Z> &months);

  struct EpochReading {
    std::shared_ptr<MechanismState> reading_state;
    std::shared_ptr<HistoricalEclipse> reading_eclipse;
    std::shared_ptr<Z> reading_cell;
    DialGlyph reading_glyph;
  };

  static std::shared_ptr<EpochReading>
  build_epoch_reading(const std::shared_ptr<Z> &epoch_year,
                      const std::shared_ptr<Z> &epoch_month,
                      std::shared_ptr<HistoricalEclipse> e);
  __attribute__((pure)) static bool
  reading_matches(const std::shared_ptr<EpochReading> &reading);
  __attribute__((pure)) static unsigned int
  reading_phase_code(const std::shared_ptr<EpochReading> &reading);
  __attribute__((pure)) static unsigned int
  reading_zodiac_code(const std::shared_ptr<EpochReading> &reading);

  struct ValidEpoch {
    std::shared_ptr<Z> ve_year;
    std::shared_ptr<Z> ve_month;
    std::shared_ptr<HistoricalEclipse> ve_eclipse;
  };

  static inline const std::shared_ptr<ValidEpoch> epoch_205_bc_valid =
      std::make_shared<ValidEpoch>(ValidEpoch{
          Z::ctor::Zneg_(
              Positive::ctor::XO_(Positive::ctor::XO_(Positive::ctor::XI_(
                  Positive::ctor::XI_(Positive::ctor::XO_(Positive::ctor::XO_(
                      Positive::ctor::XI_(Positive::ctor::XH_())))))))),
          Z::ctor::Zpos_(
              Positive::ctor::XI_(Positive::ctor::XO_(Positive::ctor::XH_()))),
          eclipse_may_205_bc});
  static inline const std::shared_ptr<EpochReading> sample_epoch_reading =
      build_epoch_reading(epoch_205_bc_valid->ve_year,
                          epoch_205_bc_valid->ve_month,
                          epoch_205_bc_valid->ve_eclipse);
  __attribute__((pure)) static unsigned int
  phase_code_after_steps(const unsigned int n);
  __attribute__((pure)) static unsigned int
  zodiac_code_after_steps(const unsigned int n);
  static inline const unsigned int sample_total_lunar_count =
      count_total_lunar(eclipse_database);
  static inline const unsigned int sample_total_lunar_visible_count =
      count_visible_total_lunar(eclipse_database);
  static inline const unsigned int sample_visible_series_checksum =
      visible_series_checksum(eclipse_database);
  static inline const bool sample_epoch_cell_zero =
      BinInt::eqb(sample_epoch_reading->reading_cell, Z::ctor::Z0_());
  static inline const bool sample_epoch_glyph_match =
      reading_matches(sample_epoch_reading);
  static inline const unsigned int sample_epoch_phase_code =
      reading_phase_code(sample_epoch_reading);
  static inline const unsigned int sample_epoch_zodiac_code =
      reading_zodiac_code(sample_epoch_reading);
  static inline const bool sample_valid_epoch_visible =
      epoch_205_bc_valid->ve_eclipse->he_visible_mediterranean;
  static inline const bool sample_valid_epoch_series_44 =
      BinInt::eqb(epoch_205_bc_valid->ve_eclipse->he_saros_series,
                  Z::ctor::Zpos_(Positive::ctor::XO_(Positive::ctor::XO_(
                      Positive::ctor::XI_(Positive::ctor::XI_(
                          Positive::ctor::XO_(Positive::ctor::XH_())))))));
  static inline const bool sample_valid_epoch_magnitude_ge_one =
      std::make_shared<Q>(
          Q{Z::ctor::Zpos_(Positive::ctor::XH_()), Positive::ctor::XH_()})
          ->Qle_bool(epoch_205_bc_valid->ve_eclipse->he_magnitude);
  static inline const bool sample_step_roundtrip_saros = BinInt::eqb(
      step_reverse(step(initial_state))->saros_dial, Z::ctor::Z0_());
  static inline const bool sample_olympiad_year_is_one_after_4 =
      BinInt::eqb(predict_olympiad_year(step_n(4u, initial_state)),
                  Z::ctor::Zpos_(Positive::ctor::XH_()));
  static inline const bool sample_eclipse_possible_after_6 =
      eclipse_possible_at_dial(step_n(6u, initial_state)->saros_dial);
  static inline const bool sample_epoch_178_misaligned = !(BinInt::eqb(
      saros_cell(Z::ctor::Zneg_(Positive::ctor::XO_(Positive::ctor::XO_(
                     Positive::ctor::XI_(Positive::ctor::XI_(
                         Positive::ctor::XO_(Positive::ctor::XO_(
                             Positive::ctor::XI_(Positive::ctor::XH_())))))))),
                 Z::ctor::Zpos_(Positive::ctor::XI_(
                     Positive::ctor::XO_(Positive::ctor::XH_()))),
                 eclipse_jun_178_bc),
      Z::ctor::Z0_()));
};

#endif // INCLUDED_EPOCH_CELL_GLYPH_TRACE
