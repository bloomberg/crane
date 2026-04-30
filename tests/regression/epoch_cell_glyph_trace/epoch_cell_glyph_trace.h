#ifndef INCLUDED_EPOCH_CELL_GLYPH_TRACE
#define INCLUDED_EPOCH_CELL_GLYPH_TRACE

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

template <typename t_A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    t_A d_a0;
    std::unique_ptr<List<t_A>> d_a1;
  };

  using variant_t = std::variant<Nil, Cons>;

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

  List<t_A> &operator=(const List<t_A> &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  List<t_A> &operator=(List<t_A> &&_other) {
    d_v_ = std::move(_other.d_v_);
    return *this;
  }

  // ACCESSORS
  List<t_A> clone() const {
    List<t_A> _out{};

    struct _CloneFrame {
      const List<t_A> *_src;
      List<t_A> *_dst;
    };

    std::vector<_CloneFrame> _stack{};
    _stack.push_back({this, &_out});
    while (!_stack.empty()) {
      auto _frame = _stack.back();
      _stack.pop_back();
      const List<t_A> *_src = _frame._src;
      List<t_A> *_dst = _frame._dst;
      if (std::holds_alternative<Nil>(_src->v())) {
        _dst->d_v_ = Nil{};
      } else {
        const auto &_alt = std::get<Cons>(_src->v());
        _dst->d_v_ = Cons{_alt.d_a0,
                          _alt.d_a1 ? std::make_unique<List<t_A>>() : nullptr};
        auto &_dst_alt = std::get<Cons>(_dst->d_v_);
        if (_alt.d_a1) {
          _stack.push_back({_alt.d_a1.get(), _dst_alt.d_a1.get()});
        }
      }
    }
    return _out;
  }

  // CREATORS
  template <typename _U> explicit List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      d_v_ = Nil{};
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<_U>::Cons>(_other.v());
      d_v_ =
          Cons{t_A(d_a0), d_a1 ? std::make_unique<List<t_A>>(*d_a1) : nullptr};
    }
  }

  static List<t_A> nil() { return List(Nil{}); }

  static List<t_A> cons(t_A a0, List<t_A> a1) {
    return List(
        Cons{std::move(a0), std::make_unique<List<t_A>>(std::move(a1))});
  }

  // MANIPULATORS
  ~List() {
    std::vector<std::unique_ptr<List<t_A>>> _stack{};
    auto _drain = [&](List<t_A> &_node) {
      if (std::holds_alternative<Cons>(_node.d_v_)) {
        auto &_alt = std::get<Cons>(_node.d_v_);
        if (_alt.d_a1) {
          _stack.push_back(std::move(_alt.d_a1));
        }
      }
    };
    _drain(*this);
    while (!_stack.empty()) {
      auto _node = std::move(_stack.back());
      _stack.pop_back();
      if (_node) {
        _drain(*_node);
      }
    }
  }

  inline variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  const variant_t &v() const { return d_v_; }
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

  Positive &operator=(const Positive &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  Positive &operator=(Positive &&_other) {
    d_v_ = std::move(_other.d_v_);
    return *this;
  }

  // ACCESSORS
  Positive clone() const {
    Positive _out{};

    struct _CloneFrame {
      const Positive *_src;
      Positive *_dst;
    };

    std::vector<_CloneFrame> _stack{};
    _stack.push_back({this, &_out});
    while (!_stack.empty()) {
      auto _frame = _stack.back();
      _stack.pop_back();
      const Positive *_src = _frame._src;
      Positive *_dst = _frame._dst;
      if (std::holds_alternative<XI>(_src->v())) {
        const auto &_alt = std::get<XI>(_src->v());
        _dst->d_v_ = XI{_alt.d_a0 ? std::make_unique<Positive>() : nullptr};
        auto &_dst_alt = std::get<XI>(_dst->d_v_);
        if (_alt.d_a0) {
          _stack.push_back({_alt.d_a0.get(), _dst_alt.d_a0.get()});
        }
      } else if (std::holds_alternative<XO>(_src->v())) {
        const auto &_alt = std::get<XO>(_src->v());
        _dst->d_v_ = XO{_alt.d_a0 ? std::make_unique<Positive>() : nullptr};
        auto &_dst_alt = std::get<XO>(_dst->d_v_);
        if (_alt.d_a0) {
          _stack.push_back({_alt.d_a0.get(), _dst_alt.d_a0.get()});
        }
      } else {
        _dst->d_v_ = XH{};
      }
    }
    return _out;
  }

  // CREATORS
  static Positive xi(Positive a0) {
    return Positive(XI{std::make_unique<Positive>(std::move(a0))});
  }

  static Positive xo(Positive a0) {
    return Positive(XO{std::make_unique<Positive>(std::move(a0))});
  }

  static Positive xh() { return Positive(XH{}); }

  // MANIPULATORS
  ~Positive() {
    std::vector<std::unique_ptr<Positive>> _stack{};
    auto _drain = [&](Positive &_node) {
      if (std::holds_alternative<XI>(_node.d_v_)) {
        auto &_alt = std::get<XI>(_node.d_v_);
        if (_alt.d_a0) {
          _stack.push_back(std::move(_alt.d_a0));
        }
      }
      if (std::holds_alternative<XO>(_node.d_v_)) {
        auto &_alt = std::get<XO>(_node.d_v_);
        if (_alt.d_a0) {
          _stack.push_back(std::move(_alt.d_a0));
        }
      }
    };
    _drain(*this);
    while (!_stack.empty()) {
      auto _node = std::move(_stack.back());
      _stack.pop_back();
      if (_node) {
        _drain(*_node);
      }
    }
  }

  inline variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  const variant_t &v() const { return d_v_; }
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

  Z &operator=(const Z &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  Z &operator=(Z &&_other) {
    d_v_ = std::move(_other.d_v_);
    return *this;
  }

  // ACCESSORS
  Z clone() const {
    auto &&_sv = *(this);
    if (std::holds_alternative<Z0>(_sv.v())) {
      return Z(Z0{});
    } else if (std::holds_alternative<Zpos>(_sv.v())) {
      const auto &[d_a0] = std::get<Zpos>(_sv.v());
      return Z(Zpos{d_a0.clone()});
    } else {
      const auto &[d_a0] = std::get<Zneg>(_sv.v());
      return Z(Zneg{d_a0.clone()});
    }
  }

  // CREATORS
  static Z z0() { return Z(Z0{}); }

  static Z zpos(Positive a0) { return Z(Zpos{std::move(a0)}); }

  static Z zneg(Positive a0) { return Z(Zneg{std::move(a0)}); }

  // MANIPULATORS
  inline variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  const variant_t &v() const { return d_v_; }
};

struct Pos {
  static Positive succ(const Positive &x);
  static Positive add(const Positive &x, const Positive &y);
  static Positive add_carry(const Positive &x, const Positive &y);
  static Positive pred_double(const Positive &x);
  static Positive mul(const Positive &x, Positive y);
  static Comparison compare_cont(const Comparison r, const Positive &x,
                                 const Positive &y);
  static Comparison compare(const Positive &_x0, const Positive &_x1);
  static bool eqb(const Positive &p, const Positive &q);

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

  static unsigned int to_nat(const Positive &x);
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
  static unsigned int to_nat(const Z &z);
  static std::pair<Z, Z> pos_div_eucl(const Positive &a, const Z &b);
  static std::pair<Z, Z> div_eucl(Z a, const Z &b);
  static Z div(const Z &a, const Z &b);
  static Z modulo(const Z &a, const Z &b);
  static Z abs(const Z &z);
};

struct Q {
  Z Qnum;
  Positive Qden;

  // ACCESSORS
  Q clone() const { return Q{(*(this)).Qnum.clone(), (*(this)).Qden.clone()}; }
};

struct QArith_base {
  static bool Qle_bool(const Q &x, const Q &y);
};

struct Datatypes {
  static Comparison CompOpp(const Comparison r);
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

  static unsigned int phase_code(const LunarPhase p);
  static LunarPhase phase_from_angle(const Z &angle_deg);
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

  static unsigned int zodiac_code(const ZodiacSign z);
  static bool eclipse_possible_at_dial(const Z &dial_pos);

  struct MechanismState {
    Z crank_position;
    Z metonic_dial;
    Z saros_dial;
    Z callippic_dial;
    Z exeligmos_dial;
    Z games_dial;
    Z zodiac_position;

    // ACCESSORS
    MechanismState clone() const {
      return MechanismState{
          (*(this)).crank_position.clone(), (*(this)).metonic_dial.clone(),
          (*(this)).saros_dial.clone(),     (*(this)).callippic_dial.clone(),
          (*(this)).exeligmos_dial.clone(), (*(this)).games_dial.clone(),
          (*(this)).zodiac_position.clone()};
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
  static MechanismState step(const MechanismState &s);
  static MechanismState step_reverse(const MechanismState &s);
  static MechanismState step_n(const unsigned int &n, MechanismState s);
  static MechanismState state_at_cell(Z cell);
  static LunarPhase predict_moon_phase_from_state(const MechanismState &s);
  static Z predict_olympiad_year(const MechanismState &s);
  static ZodiacSign predict_zodiac_sign(const MechanismState &s);
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

  static unsigned int eclipse_category_code(const EclipseCategory c);

  struct HistoricalEclipse {
    Z he_year;
    Z he_month;
    Z he_day;
    EclipseCategory he_category;
    Z he_saros_series;
    Z he_saros_member;
    Q he_magnitude;
    bool he_visible_mediterranean;

    // ACCESSORS
    HistoricalEclipse clone() const {
      return HistoricalEclipse{(*(this)).he_year.clone(),
                               (*(this)).he_month.clone(),
                               (*(this)).he_day.clone(),
                               (*(this)).he_category,
                               (*(this)).he_saros_series.clone(),
                               (*(this)).he_saros_member.clone(),
                               (*(this)).he_magnitude.clone(),
                               (*(this)).he_visible_mediterranean};
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

  static unsigned int glyph_code(const DialGlyph g);
  static bool category_matches_glyph(const EclipseCategory cat,
                                     const DialGlyph g);
  static DialGlyph glyph_at_cell(const Z &cell);
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
  static unsigned int count_total_lunar(const List<HistoricalEclipse> &es);
  static unsigned int
  count_visible_total_lunar(const List<HistoricalEclipse> &es);
  static unsigned int
  visible_series_checksum(const List<HistoricalEclipse> &es);
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

    // ACCESSORS
    EpochReading clone() const {
      return EpochReading{
          (*(this)).reading_state.clone(), (*(this)).reading_eclipse.clone(),
          (*(this)).reading_cell.clone(), (*(this)).reading_glyph};
    }
  };

  static EpochReading build_epoch_reading(const Z &epoch_year,
                                          const Z &epoch_month,
                                          HistoricalEclipse e);
  static bool reading_matches(const EpochReading &reading);
  static unsigned int reading_phase_code(const EpochReading &reading);
  static unsigned int reading_zodiac_code(const EpochReading &reading);

  struct ValidEpoch {
    Z ve_year;
    Z ve_month;
    HistoricalEclipse ve_eclipse;

    // ACCESSORS
    ValidEpoch clone() const {
      return ValidEpoch{(*(this)).ve_year.clone(), (*(this)).ve_month.clone(),
                        (*(this)).ve_eclipse.clone()};
    }
  };

  static inline const ValidEpoch epoch_205_bc_valid = ValidEpoch{
      Z::zneg(Positive::xo(Positive::xo(Positive::xi(Positive::xi(
          Positive::xo(Positive::xo(Positive::xi(Positive::xh())))))))),
      Z::zpos(Positive::xi(Positive::xo(Positive::xh()))), eclipse_may_205_bc};
  static inline const EpochReading sample_epoch_reading = build_epoch_reading(
      epoch_205_bc_valid.ve_year, epoch_205_bc_valid.ve_month,
      epoch_205_bc_valid.ve_eclipse);
  static unsigned int phase_code_after_steps(const unsigned int &n);
  static unsigned int zodiac_code_after_steps(const unsigned int &n);
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
