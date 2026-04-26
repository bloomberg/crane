#ifndef INCLUDED_EPOCH_CELL_GLYPH_TRACE
#define INCLUDED_EPOCH_CELL_GLYPH_TRACE

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

template <typename T> struct is_unique_ptr : std::false_type {};

template <typename T>
struct is_unique_ptr<std::unique_ptr<T>> : std::true_type {
  using element_type = T;
};

template <typename T> auto clone_value(const T &x) { return x; }

template <typename T>
std::unique_ptr<T> clone_value(const std::unique_ptr<T> &x) {
  if constexpr (requires { x->clone(); }) {
    return x ? std::make_unique<T>(x->clone()) : nullptr;
  } else {
    return x ? std::make_unique<T>(*x) : nullptr;
  }
}

template <typename Target, typename Source>
Target clone_as_value(const Source &x) {
  using T = std::remove_cvref_t<Target>;
  using S = std::remove_cvref_t<Source>;
  if constexpr (requires(const S &s) {
                  s.has_value();
                  *s;
                }) {
    if (!x.has_value())
      return T{};
    using TInner = std::remove_cvref_t<decltype(*std::declval<const T &>())>;
    return T{clone_as_value<TInner>(*x)};
  } else if constexpr (std::is_same_v<T, S>) {
    if constexpr (is_unique_ptr<T>::value) {
      return clone_value(x);
    } else if constexpr (requires { x.clone(); }) {
      return x.clone();
    } else {
      return x;
    }
  } else if constexpr (is_unique_ptr<S>::value) {
    if (!x)
      return T{};
    return clone_as_value<T>(*x);
  } else if constexpr (is_unique_ptr<T>::value) {
    using Inner = typename is_unique_ptr<T>::element_type;
    return std::make_unique<Inner>(clone_as_value<Inner>(x));
  } else {
    return T(x);
  }
}

template <typename t_A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    t_A d_a0;
    std::unique_ptr<List<t_A>> d_a1;
  };

  using variant_t = std::variant<Nil, Cons>;
  using crane_element_type = t_A;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  List() {}

  explicit List(Nil _v) : d_v_(_v) {}

  explicit List(Cons _v) : d_v_(std::move(_v)) {}

  List(const List<t_A> &_other) : d_v_(std::move(_other.clone().d_v_)) {}

  List(List<t_A> &&_other) : d_v_(std::move(_other.d_v_)) {}

  __attribute__((pure)) List<t_A> &operator=(const List<t_A> &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  __attribute__((pure)) List<t_A> &operator=(List<t_A> &&_other) {
    d_v_ = std::move(_other.d_v_);
    return *this;
  }

  // ACCESSORS
  __attribute__((pure)) List<t_A> clone() const {
    auto &&_sv = *(this);
    if (std::holds_alternative<Nil>(_sv.v())) {
      return List<t_A>(Nil{});
    } else {
      const auto &[d_a0, d_a1] = std::get<Cons>(_sv.v());
      return List<t_A>(Cons{clone_value(d_a0), clone_value(d_a1)});
    }
  }

  // CREATORS
  template <typename _U> explicit List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      d_v_ = Nil{};
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<_U>::Cons>(_other.v());
      d_v_ = Cons{clone_as_value<t_A>(d_a0),
                  d_a1 ? std::make_unique<List<t_A>>(*d_a1) : nullptr};
    }
  }

  __attribute__((pure)) static List<t_A> nil() { return List(Nil{}); }

  __attribute__((pure)) static List<t_A> cons(t_A a0, const List<t_A> &a1) {
    return List(Cons{std::move(a0), std::make_unique<List<t_A>>(a1)});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) List<t_A> *operator->() { return this; }

  __attribute__((pure)) const List<t_A> *operator->() const { return this; }

  __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

  __attribute__((pure)) bool operator==(std::nullptr_t) const { return false; }

  // MANIPULATORS
  void reset() { *this = List<t_A>(); }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
};
enum class Comparison { e_EQ, e_LT, e_GT };

struct Positive {
  // TYPES
  struct XI {
    std::unique_ptr<Positive> d_a0;
  };

  struct XO {
    std::unique_ptr<Positive> d_a0;
  };

  struct XH {};

  using variant_t = std::variant<XI, XO, XH>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  Positive() {}

  explicit Positive(XI _v) : d_v_(std::move(_v)) {}

  explicit Positive(XO _v) : d_v_(std::move(_v)) {}

  explicit Positive(XH _v) : d_v_(_v) {}

  Positive(const Positive &_other) : d_v_(std::move(_other.clone().d_v_)) {}

  Positive(Positive &&_other) : d_v_(std::move(_other.d_v_)) {}

  __attribute__((pure)) Positive &operator=(const Positive &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  __attribute__((pure)) Positive &operator=(Positive &&_other) {
    d_v_ = std::move(_other.d_v_);
    return *this;
  }

  // ACCESSORS
  __attribute__((pure)) Positive clone() const {
    auto &&_sv = *(this);
    if (std::holds_alternative<XI>(_sv.v())) {
      const auto &[d_a0] = std::get<XI>(_sv.v());
      return Positive(XI{clone_value(d_a0)});
    } else if (std::holds_alternative<XO>(_sv.v())) {
      const auto &[d_a0] = std::get<XO>(_sv.v());
      return Positive(XO{clone_value(d_a0)});
    } else {
      return Positive(XH{});
    }
  }

  // CREATORS
  __attribute__((pure)) static Positive xi(const Positive &a0) {
    return Positive(XI{std::make_unique<Positive>(a0)});
  }

  __attribute__((pure)) static Positive xo(const Positive &a0) {
    return Positive(XO{std::make_unique<Positive>(a0)});
  }

  __attribute__((pure)) static Positive xh() { return Positive(XH{}); }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) Positive *operator->() { return this; }

  __attribute__((pure)) const Positive *operator->() const { return this; }

  __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

  __attribute__((pure)) bool operator==(std::nullptr_t) const { return false; }

  // MANIPULATORS
  void reset() { *this = Positive(); }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
};

struct Z {
  // TYPES
  struct Z0 {};

  struct Zpos {
    Positive d_a0;
  };

  struct Zneg {
    Positive d_a0;
  };

  using variant_t = std::variant<Z0, Zpos, Zneg>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  Z() {}

  explicit Z(Z0 _v) : d_v_(_v) {}

  explicit Z(Zpos _v) : d_v_(std::move(_v)) {}

  explicit Z(Zneg _v) : d_v_(std::move(_v)) {}

  Z(const Z &_other) : d_v_(std::move(_other.clone().d_v_)) {}

  Z(Z &&_other) : d_v_(std::move(_other.d_v_)) {}

  __attribute__((pure)) Z &operator=(const Z &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  __attribute__((pure)) Z &operator=(Z &&_other) {
    d_v_ = std::move(_other.d_v_);
    return *this;
  }

  // ACCESSORS
  __attribute__((pure)) Z clone() const {
    auto &&_sv = *(this);
    if (std::holds_alternative<Z0>(_sv.v())) {
      return Z(Z0{});
    } else if (std::holds_alternative<Zpos>(_sv.v())) {
      const auto &[d_a0] = std::get<Zpos>(_sv.v());
      return Z(Zpos{d_a0});
    } else {
      const auto &[d_a0] = std::get<Zneg>(_sv.v());
      return Z(Zneg{d_a0});
    }
  }

  // CREATORS
  constexpr static Z z0() { return Z(Z0{}); }

  __attribute__((pure)) static Z zpos(Positive a0) {
    return Z(Zpos{std::move(a0)});
  }

  __attribute__((pure)) static Z zneg(Positive a0) {
    return Z(Zneg{std::move(a0)});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) Z *operator->() { return this; }

  __attribute__((pure)) const Z *operator->() const { return this; }

  __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

  __attribute__((pure)) bool operator==(std::nullptr_t) const { return false; }

  // MANIPULATORS
  void reset() { *this = Z(); }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
};

struct Pos {
  __attribute__((pure)) static Positive succ(const Positive &x);
  __attribute__((pure)) static Positive add(const Positive &x,
                                            const Positive &y);
  __attribute__((pure)) static Positive add_carry(const Positive &x,
                                                  const Positive &y);
  __attribute__((pure)) static Positive pred_double(const Positive &x);
  __attribute__((pure)) static Positive mul(const Positive &x, Positive y);
  __attribute__((pure)) static Comparison
  compare_cont(const Comparison r, const Positive &x, const Positive &y);
  __attribute__((pure)) static Comparison compare(const Positive &_x0,
                                                  const Positive &_x1);
  __attribute__((pure)) static bool eqb(const Positive &p, const Positive &q);

  template <typename T1, MapsTo<T1, T1, T1> F0>
  static T1 iter_op(F0 &&op, const Positive &p, const T1 a) {
    if (std::holds_alternative<typename Positive::XI>(p.v())) {
      const auto &[d_a0] = std::get<typename Positive::XI>(p.v());
      return op(a, iter_op<T1>(op, *(d_a0), op(a, a)));
    } else if (std::holds_alternative<typename Positive::XO>(p.v())) {
      const auto &[d_a0] = std::get<typename Positive::XO>(p.v());
      return iter_op<T1>(op, *(d_a0), op(a, a));
    } else {
      return a;
    }
  }

  __attribute__((pure)) static unsigned int to_nat(const Positive &x);
};

struct BinInt {
  __attribute__((pure)) static Z double_(const Z &x);
  __attribute__((pure)) static Z succ_double(const Z &x);
  __attribute__((pure)) static Z pred_double(const Z &x);
  __attribute__((pure)) static Z pos_sub(const Positive &x, const Positive &y);
  __attribute__((pure)) static Z add(Z x, Z y);
  __attribute__((pure)) static Z opp(const Z &x);
  __attribute__((pure)) static Z sub(const Z &m, const Z &n);
  __attribute__((pure)) static Z mul(const Z &x, const Z &y);
  __attribute__((pure)) static Comparison compare(const Z &x, const Z &y);
  __attribute__((pure)) static bool leb(const Z &x, const Z &y);
  __attribute__((pure)) static bool ltb(const Z &x, const Z &y);
  __attribute__((pure)) static bool eqb(const Z &x, const Z &y);
  __attribute__((pure)) static unsigned int to_nat(const Z &z);
  __attribute__((pure)) static std::pair<Z, Z> pos_div_eucl(const Positive &a,
                                                            const Z &b);
  __attribute__((pure)) static std::pair<Z, Z> div_eucl(Z a, const Z &b);
  __attribute__((pure)) static Z div(const Z &a, const Z &b);
  __attribute__((pure)) static Z modulo(const Z &a, const Z &b);
  __attribute__((pure)) static Z abs(const Z &z);
};

struct Q {
  Z Qnum;
  Positive Qden;

  __attribute__((pure)) Q *operator->() { return this; }

  __attribute__((pure)) const Q *operator->() const { return this; }

  // ACCESSORS
  __attribute__((pure)) Q clone() const {
    return Q{(*(this)).Qnum, (*(this)).Qden};
  }
};

struct QArith_base {
  __attribute__((pure)) static bool Qle_bool(const Q &x, const Q &y);
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
    default:
      std::unreachable();
    }
  }

  template <typename T1>
  static T1 LunarPhase_rec(const T1 f, const T1 f0, const T1 f1, const T1 f2,
                           const LunarPhase l) {
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
    default:
      std::unreachable();
    }
  }

  __attribute__((pure)) static unsigned int phase_code(const LunarPhase p);
  __attribute__((pure)) static LunarPhase phase_from_angle(const Z &angle_deg);
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
    default:
      std::unreachable();
    }
  }

  template <typename T1>
  static T1 ZodiacSign_rec(const T1 f, const T1 f0, const T1 f1, const T1 f2,
                           const T1 f3, const T1 f4, const T1 f5, const T1 f6,
                           const T1 f7, const T1 f8, const T1 f9, const T1 f10,
                           const ZodiacSign z) {
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
    default:
      std::unreachable();
    }
  }

  __attribute__((pure)) static unsigned int zodiac_code(const ZodiacSign z);
  __attribute__((pure)) static bool eclipse_possible_at_dial(const Z &dial_pos);

  struct MechanismState {
    Z crank_position;
    Z metonic_dial;
    Z saros_dial;
    Z callippic_dial;
    Z exeligmos_dial;
    Z games_dial;
    Z zodiac_position;

    __attribute__((pure)) MechanismState *operator->() { return this; }

    __attribute__((pure)) const MechanismState *operator->() const {
      return this;
    }

    // ACCESSORS
    __attribute__((pure)) MechanismState clone() const {
      return MechanismState{(*(this)).crank_position, (*(this)).metonic_dial,
                            (*(this)).saros_dial,     (*(this)).callippic_dial,
                            (*(this)).exeligmos_dial, (*(this)).games_dial,
                            (*(this)).zodiac_position};
    }
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
  __attribute__((pure)) static MechanismState step(const MechanismState &s);
  __attribute__((pure)) static MechanismState
  step_reverse(const MechanismState &s);
  __attribute__((pure)) static MechanismState step_n(const unsigned int &n,
                                                     MechanismState s);
  __attribute__((pure)) static MechanismState state_at_cell(Z cell);
  __attribute__((pure)) static LunarPhase
  predict_moon_phase_from_state(const MechanismState &s);
  __attribute__((pure)) static Z predict_olympiad_year(const MechanismState &s);
  __attribute__((pure)) static ZodiacSign
  predict_zodiac_sign(const MechanismState &s);
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
    default:
      std::unreachable();
    }
  }

  template <typename T1>
  static T1 EclipseCategory_rec(const T1 f, const T1 f0, const T1 f1,
                                const T1 f2, const T1 f3,
                                const EclipseCategory e) {
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
    default:
      std::unreachable();
    }
  }

  __attribute__((pure)) static unsigned int
  eclipse_category_code(const EclipseCategory c);

  struct HistoricalEclipse {
    Z he_year;
    Z he_month;
    Z he_day;
    EclipseCategory he_category;
    Z he_saros_series;
    Z he_saros_member;
    Q he_magnitude;
    bool he_visible_mediterranean;

    __attribute__((pure)) HistoricalEclipse *operator->() { return this; }

    __attribute__((pure)) const HistoricalEclipse *operator->() const {
      return this;
    }

    // ACCESSORS
    __attribute__((pure)) HistoricalEclipse clone() const {
      return HistoricalEclipse{
          (*(this)).he_year,         (*(this)).he_month,
          (*(this)).he_day,          (*(this)).he_category,
          (*(this)).he_saros_series, (*(this)).he_saros_member,
          (*(this)).he_magnitude,    (*(this)).he_visible_mediterranean};
    }
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
    default:
      std::unreachable();
    }
  }

  template <typename T1>
  static T1 DialGlyph_rec(const T1 f, const T1 f0, const T1 f1, const T1 f2,
                          const T1 f3, const DialGlyph d) {
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
    default:
      std::unreachable();
    }
  }

  __attribute__((pure)) static unsigned int glyph_code(const DialGlyph g);
  __attribute__((pure)) static bool
  category_matches_glyph(const EclipseCategory cat, const DialGlyph g);
  __attribute__((pure)) static DialGlyph glyph_at_cell(const Z &cell);
  static inline const HistoricalEclipse eclipse_may_205_bc = HistoricalEclipse{
      Z::zneg(Positive::xo(Positive::xo(Positive::xi(Positive::xi(
          Positive::xo(Positive::xo(Positive::xi(Positive::xh())))))))),
      Z::zpos(Positive::xi(Positive::xo(Positive::xh()))),
      Z::zpos(Positive::xo(Positive::xo(Positive::xi(Positive::xh())))),
      EclipseCategory::e_EC_TOTALLUNAR,
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
      EclipseCategory::e_EC_TOTALLUNAR,
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
      EclipseCategory::e_EC_PARTIALSOLAR,
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
      EclipseCategory::e_EC_TOTALLUNAR,
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
      EclipseCategory::e_EC_TOTALLUNAR,
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
      EclipseCategory::e_EC_TOTALLUNAR,
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
  __attribute__((pure)) static unsigned int
  count_total_lunar(const List<HistoricalEclipse> &es);
  __attribute__((pure)) static unsigned int
  count_visible_total_lunar(const List<HistoricalEclipse> &es);
  __attribute__((pure)) static unsigned int
  visible_series_checksum(const List<HistoricalEclipse> &es);
  __attribute__((pure)) static Z months_from_epoch(const Z &epoch_year,
                                                   const Z &eclipse_year,
                                                   const Z &epoch_month,
                                                   const Z &eclipse_month);
  __attribute__((pure)) static Z saros_cell(const Z &epoch_year,
                                            const Z &epoch_month,
                                            const HistoricalEclipse &e);
  __attribute__((pure)) static Z saros_dial_at_month(const Z &start_cell,
                                                     const Z &months);

  struct EpochReading {
    MechanismState reading_state;
    HistoricalEclipse reading_eclipse;
    Z reading_cell;
    DialGlyph reading_glyph;

    __attribute__((pure)) EpochReading *operator->() { return this; }

    __attribute__((pure)) const EpochReading *operator->() const {
      return this;
    }

    // ACCESSORS
    __attribute__((pure)) EpochReading clone() const {
      return EpochReading{(*(this)).reading_state, (*(this)).reading_eclipse,
                          (*(this)).reading_cell, (*(this)).reading_glyph};
    }
  };

  __attribute__((pure)) static EpochReading
  build_epoch_reading(const Z &epoch_year, const Z &epoch_month,
                      HistoricalEclipse e);
  __attribute__((pure)) static bool
  reading_matches(const EpochReading &reading);
  __attribute__((pure)) static unsigned int
  reading_phase_code(const EpochReading &reading);
  __attribute__((pure)) static unsigned int
  reading_zodiac_code(const EpochReading &reading);

  struct ValidEpoch {
    Z ve_year;
    Z ve_month;
    HistoricalEclipse ve_eclipse;

    __attribute__((pure)) ValidEpoch *operator->() { return this; }

    __attribute__((pure)) const ValidEpoch *operator->() const { return this; }

    // ACCESSORS
    __attribute__((pure)) ValidEpoch clone() const {
      return ValidEpoch{(*(this)).ve_year, (*(this)).ve_month,
                        (*(this)).ve_eclipse};
    }
  };

  static inline const ValidEpoch epoch_205_bc_valid = ValidEpoch{
      Z::zneg(Positive::xo(Positive::xo(Positive::xi(Positive::xi(
          Positive::xo(Positive::xo(Positive::xi(Positive::xh())))))))),
      Z::zpos(Positive::xi(Positive::xo(Positive::xh()))), eclipse_may_205_bc};
  static inline const EpochReading sample_epoch_reading = build_epoch_reading(
      epoch_205_bc_valid.ve_year, epoch_205_bc_valid.ve_month,
      epoch_205_bc_valid.ve_eclipse);
  __attribute__((pure)) static unsigned int
  phase_code_after_steps(const unsigned int &n);
  __attribute__((pure)) static unsigned int
  zodiac_code_after_steps(const unsigned int &n);
  static inline const unsigned int sample_total_lunar_count =
      count_total_lunar(eclipse_database);
  static inline const unsigned int sample_total_lunar_visible_count =
      count_visible_total_lunar(eclipse_database);
  static inline const unsigned int sample_visible_series_checksum =
      visible_series_checksum(eclipse_database);
  static inline const bool sample_epoch_cell_zero =
      BinInt::eqb(sample_epoch_reading.reading_cell, Z::z0());
  static inline const bool sample_epoch_glyph_match =
      reading_matches(sample_epoch_reading);
  static inline const unsigned int sample_epoch_phase_code =
      reading_phase_code(sample_epoch_reading);
  static inline const unsigned int sample_epoch_zodiac_code =
      reading_zodiac_code(sample_epoch_reading);
  static inline const bool sample_valid_epoch_visible =
      epoch_205_bc_valid.ve_eclipse.he_visible_mediterranean;
  static inline const bool sample_valid_epoch_series_44 =
      BinInt::eqb(epoch_205_bc_valid.ve_eclipse.he_saros_series,
                  Z::zpos(Positive::xo(Positive::xo(Positive::xi(
                      Positive::xi(Positive::xo(Positive::xh())))))));
  static inline const bool sample_valid_epoch_magnitude_ge_one =
      QArith_base::Qle_bool(Q{Z::zpos(Positive::xh()), Positive::xh()},
                            epoch_205_bc_valid.ve_eclipse.he_magnitude);
  static inline const bool sample_step_roundtrip_saros =
      BinInt::eqb(step_reverse(step(initial_state)).saros_dial, Z::z0());
  static inline const bool sample_olympiad_year_is_one_after_4 =
      BinInt::eqb(predict_olympiad_year(step_n(4u, initial_state)),
                  Z::zpos(Positive::xh()));
  static inline const bool sample_eclipse_possible_after_6 =
      eclipse_possible_at_dial(step_n(6u, initial_state).saros_dial);
  static inline const bool sample_epoch_178_misaligned = !(BinInt::eqb(
      saros_cell(
          Z::zneg(Positive::xo(Positive::xo(Positive::xi(Positive::xi(
              Positive::xo(Positive::xo(Positive::xi(Positive::xh())))))))),
          Z::zpos(Positive::xi(Positive::xo(Positive::xh()))),
          eclipse_jun_178_bc),
      Z::z0()));
};

#endif // INCLUDED_EPOCH_CELL_GLYPH_TRACE
