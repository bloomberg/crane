#ifndef INCLUDED_COALITION_BID_HONOR_TRACE
#define INCLUDED_COALITION_BID_HONOR_TRACE

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

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
  __attribute__((pure)) List<t_A> clone() const {
    auto &&_sv = *(this);
    if (std::holds_alternative<Nil>(_sv.v())) {
      return List<t_A>(Nil{});
    } else {
      const auto &[d_a0, d_a1] = std::get<Cons>(_sv.v());
      return List<t_A>(Cons{
          d_a0, d_a1 ? std::make_unique<List<t_A>>(d_a1->clone()) : nullptr});
    }
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

  __attribute__((pure)) static List<t_A> nil() { return List(Nil{}); }

  __attribute__((pure)) static List<t_A> cons(t_A a0, const List<t_A> &a1) {
    return List(Cons{std::move(a0), std::make_unique<List<t_A>>(a1)});
  }

  // MANIPULATORS
  inline variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }

  template <MapsTo<bool, t_A> F0>
  __attribute__((pure)) bool existsb(F0 &&f) const {
    auto &&_sv = *(this);
    if (std::holds_alternative<typename List<t_A>::Nil>(_sv.v())) {
      return false;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<t_A>::Cons>(_sv.v());
      return (f(d_a0) || (*(d_a1)).existsb(f));
    }
  }

  template <typename T1, MapsTo<T1, t_A, T1> F0>
  T1 fold_right(F0 &&f, const T1 a0) const {
    auto &&_sv = *(this);
    if (std::holds_alternative<typename List<t_A>::Nil>(_sv.v())) {
      return a0;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<t_A>::Cons>(_sv.v());
      return f(d_a0, (*(d_a1)).template fold_right<T1>(f, a0));
    }
  }

  template <typename T1, MapsTo<List<T1>, t_A> F0>
  __attribute__((pure)) List<T1> flat_map(F0 &&f) const {
    auto &&_sv = *(this);
    if (std::holds_alternative<typename List<t_A>::Nil>(_sv.v())) {
      return List<T1>::nil();
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<t_A>::Cons>(_sv.v());
      return f(d_a0).app((*(d_a1)).template flat_map<T1>(f));
    }
  }

  template <typename T1, MapsTo<T1, t_A> F0>
  __attribute__((pure)) List<T1> map(F0 &&f) const {
    auto &&_sv = *(this);
    if (std::holds_alternative<typename List<t_A>::Nil>(_sv.v())) {
      return List<T1>::nil();
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<t_A>::Cons>(_sv.v());
      return List<T1>::cons(f(d_a0), (*(d_a1)).template map<T1>(f));
    }
  }

  __attribute__((pure)) unsigned int length() const {
    auto &&_sv = *(this);
    if (std::holds_alternative<typename List<t_A>::Nil>(_sv.v())) {
      return 0u;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<t_A>::Cons>(_sv.v());
      return ((*(d_a1)).length() + 1);
    }
  }

  __attribute__((pure)) List<t_A> app(List<t_A> m) const {
    auto &&_sv = *(this);
    if (std::holds_alternative<typename List<t_A>::Nil>(_sv.v())) {
      return m;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<t_A>::Cons>(_sv.v());
      return List<t_A>::cons(d_a0, (*(d_a1)).app(m));
    }
  }
};

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
  __attribute__((pure)) Positive clone() const {
    auto &&_sv = *(this);
    if (std::holds_alternative<XI>(_sv.v())) {
      const auto &[d_a0] = std::get<XI>(_sv.v());
      return Positive(
          XI{d_a0 ? std::make_unique<Positive>(d_a0->clone()) : nullptr});
    } else if (std::holds_alternative<XO>(_sv.v())) {
      const auto &[d_a0] = std::get<XO>(_sv.v());
      return Positive(
          XO{d_a0 ? std::make_unique<Positive>(d_a0->clone()) : nullptr});
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
  inline variant_t &v_mut() { return d_v_; }

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

  Z &operator=(const Z &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  Z &operator=(Z &&_other) {
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
      return Z(Zpos{d_a0.clone()});
    } else {
      const auto &[d_a0] = std::get<Zneg>(_sv.v());
      return Z(Zneg{d_a0.clone()});
    }
  }

  // CREATORS
  __attribute__((pure)) static Z z0() { return Z(Z0{}); }

  __attribute__((pure)) static Z zpos(Positive a0) {
    return Z(Zpos{std::move(a0)});
  }

  __attribute__((pure)) static Z zneg(Positive a0) {
    return Z(Zneg{std::move(a0)});
  }

  // MANIPULATORS
  inline variant_t &v_mut() { return d_v_; }

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
  __attribute__((pure)) static bool eqb(const Positive &p, const Positive &q);
};

struct BinInt {
  __attribute__((pure)) static Z double_(const Z &x);
  __attribute__((pure)) static Z succ_double(const Z &x);
  __attribute__((pure)) static Z pred_double(const Z &x);
  __attribute__((pure)) static Z pos_sub(const Positive &x, const Positive &y);
  __attribute__((pure)) static Z add(Z x, Z y);
  __attribute__((pure)) static bool eqb(const Z &x, const Z &y);
};

struct ListDef {
  template <typename T1>
  static T1 nth(const unsigned int &n, const List<T1> &l, const T1 default0);
};

struct CoalitionBidHonorTraceCase {
  enum class Clan { e_CLANWOLF, e_CLANJADEFALCON, e_CLANGHOSTBEAR };

  template <typename T1>
  static T1 Clan_rect(const T1 f, const T1 f0, const T1 f1, const Clan c) {
    switch (c) {
    case Clan::e_CLANWOLF: {
      return f;
    }
    case Clan::e_CLANJADEFALCON: {
      return f0;
    }
    case Clan::e_CLANGHOSTBEAR: {
      return f1;
    }
    default:
      std::unreachable();
    }
  }

  template <typename T1>
  static T1 Clan_rec(const T1 f, const T1 f0, const T1 f1, const Clan c) {
    switch (c) {
    case Clan::e_CLANWOLF: {
      return f;
    }
    case Clan::e_CLANJADEFALCON: {
      return f0;
    }
    case Clan::e_CLANGHOSTBEAR: {
      return f1;
    }
    default:
      std::unreachable();
    }
  }

  __attribute__((pure)) static bool clan_eq_dec(const Clan c1, const Clan c2);
  __attribute__((pure)) static bool clan_eqb(const Clan c1, const Clan c2);
  enum class Rank { e_WARRIOR, e_STARCAPTAIN, e_STARCOLONEL };

  template <typename T1>
  static T1 Rank_rect(const T1 f, const T1 f0, const T1 f1, const Rank r) {
    switch (r) {
    case Rank::e_WARRIOR: {
      return f;
    }
    case Rank::e_STARCAPTAIN: {
      return f0;
    }
    case Rank::e_STARCOLONEL: {
      return f1;
    }
    default:
      std::unreachable();
    }
  }

  template <typename T1>
  static T1 Rank_rec(const T1 f, const T1 f0, const T1 f1, const Rank r) {
    switch (r) {
    case Rank::e_WARRIOR: {
      return f;
    }
    case Rank::e_STARCAPTAIN: {
      return f0;
    }
    case Rank::e_STARCOLONEL: {
      return f1;
    }
    default:
      std::unreachable();
    }
  }

  __attribute__((pure)) static unsigned int rank_to_nat(const Rank r);
  __attribute__((pure)) static bool rank_le(const Rank r1, const Rank r2);

  struct Commander {
    unsigned int cmd_id;
    Clan cmd_clan;
    Rank cmd_rank;
    bool cmd_bloodnamed;

    // ACCESSORS
    __attribute__((pure)) Commander clone() const {
      return Commander{(*(this)).cmd_id, (*(this)).cmd_clan, (*(this)).cmd_rank,
                       (*(this)).cmd_bloodnamed};
    }
  };

  __attribute__((pure)) static bool may_issue_batchall(const Commander &c);
  enum class UnitClass { e_OMNIMECH, e_BATTLEMECH, e_ELEMENTAL };

  template <typename T1>
  static T1 UnitClass_rect(const T1 f, const T1 f0, const T1 f1,
                           const UnitClass u) {
    switch (u) {
    case UnitClass::e_OMNIMECH: {
      return f;
    }
    case UnitClass::e_BATTLEMECH: {
      return f0;
    }
    case UnitClass::e_ELEMENTAL: {
      return f1;
    }
    default:
      std::unreachable();
    }
  }

  template <typename T1>
  static T1 UnitClass_rec(const T1 f, const T1 f0, const T1 f1,
                          const UnitClass u) {
    switch (u) {
    case UnitClass::e_OMNIMECH: {
      return f;
    }
    case UnitClass::e_BATTLEMECH: {
      return f0;
    }
    case UnitClass::e_ELEMENTAL: {
      return f1;
    }
    default:
      std::unreachable();
    }
  }
  enum class WeightClass { e_LIGHT, e_HEAVY, e_ASSAULT };

  template <typename T1>
  static T1 WeightClass_rect(const T1 f, const T1 f0, const T1 f1,
                             const WeightClass w) {
    switch (w) {
    case WeightClass::e_LIGHT: {
      return f;
    }
    case WeightClass::e_HEAVY: {
      return f0;
    }
    case WeightClass::e_ASSAULT: {
      return f1;
    }
    default:
      std::unreachable();
    }
  }

  template <typename T1>
  static T1 WeightClass_rec(const T1 f, const T1 f0, const T1 f1,
                            const WeightClass w) {
    switch (w) {
    case WeightClass::e_LIGHT: {
      return f;
    }
    case WeightClass::e_HEAVY: {
      return f0;
    }
    case WeightClass::e_ASSAULT: {
      return f1;
    }
    default:
      std::unreachable();
    }
  }

  __attribute__((pure)) static unsigned int
  weight_class_value(const WeightClass w);
  __attribute__((pure)) static unsigned int unit_class_bonus(const UnitClass c);

  struct Unit {
    unsigned int unit_id;
    UnitClass unit_class;
    WeightClass unit_weight;
    unsigned int unit_tonnage;
    unsigned int unit_gunnery;
    unsigned int unit_piloting;
    bool unit_is_elite;
    bool unit_is_clan;

    // ACCESSORS
    __attribute__((pure)) Unit clone() const {
      return Unit{(*(this)).unit_id,       (*(this)).unit_class,
                  (*(this)).unit_weight,   (*(this)).unit_tonnage,
                  (*(this)).unit_gunnery,  (*(this)).unit_piloting,
                  (*(this)).unit_is_elite, (*(this)).unit_is_clan};
    }
  };

  __attribute__((pure)) static unsigned int unit_skill(const Unit &u);
  __attribute__((pure)) static unsigned int
  skill_bv_multiplier_num(const unsigned int &skill);
  __attribute__((pure)) static unsigned int unit_base_bv(const Unit &u);
  __attribute__((pure)) static unsigned int unit_tech_bv(const Unit &u);
  __attribute__((pure)) static unsigned int unit_battle_value(const Unit &u);
  __attribute__((pure)) static unsigned int
  unit_effective_combat_rating(const Unit &u);
  using Force = List<Unit>;

  struct ForceMetrics {
    unsigned int fm_count;
    unsigned int fm_tonnage;
    unsigned int fm_elite_count;
    unsigned int fm_clan_count;
    unsigned int fm_total_bv;
    unsigned int fm_total_ecr;

    // ACCESSORS
    __attribute__((pure)) ForceMetrics clone() const {
      return ForceMetrics{(*(this)).fm_count,       (*(this)).fm_tonnage,
                          (*(this)).fm_elite_count, (*(this)).fm_clan_count,
                          (*(this)).fm_total_bv,    (*(this)).fm_total_ecr};
    }
  };

  static inline const ForceMetrics empty_metrics =
      ForceMetrics{0u, 0u, 0u, 0u, 0u, 0u};
  __attribute__((pure)) static ForceMetrics unit_to_metrics(const Unit &u);
  __attribute__((pure)) static ForceMetrics metrics_add(const ForceMetrics &m1,
                                                        const ForceMetrics &m2);
  __attribute__((pure)) static ForceMetrics force_metrics(const List<Unit> &f);
  __attribute__((pure)) static bool metrics_total_lt(const ForceMetrics &m1,
                                                     const ForceMetrics &m2);
  enum class Side { e_ATTACKER, e_DEFENDER };

  template <typename T1>
  static T1 Side_rect(const T1 f, const T1 f0, const Side s) {
    switch (s) {
    case Side::e_ATTACKER: {
      return f;
    }
    case Side::e_DEFENDER: {
      return f0;
    }
    default:
      std::unreachable();
    }
  }

  template <typename T1>
  static T1 Side_rec(const T1 f, const T1 f0, const Side s) {
    switch (s) {
    case Side::e_ATTACKER: {
      return f;
    }
    case Side::e_DEFENDER: {
      return f0;
    }
    default:
      std::unreachable();
    }
  }

  struct CoalitionMember {
    Clan cm_clan;
    Commander cm_commander;
    Force cm_force;

    // ACCESSORS
    __attribute__((pure)) CoalitionMember clone() const {
      return CoalitionMember{(*(this)).cm_clan, (*(this)).cm_commander.clone(),
                             (*(this)).cm_force};
    }
  };

  using Coalition = List<CoalitionMember>;
  __attribute__((pure)) static Force
  coalition_force(const List<CoalitionMember> &c);
  __attribute__((pure)) static ForceMetrics
  coalition_metrics(const List<CoalitionMember> &c);
  __attribute__((pure)) static bool
  coalition_contains_clan(const List<CoalitionMember> &c, const Clan clan);
  __attribute__((pure)) static unsigned int
  coalition_tonnage(const List<CoalitionMember> &c);

  struct CoalitionMemberBid {
    unsigned int cmb_member_index;
    Force cmb_new_force;
    Side cmb_side;

    // ACCESSORS
    __attribute__((pure)) CoalitionMemberBid clone() const {
      return CoalitionMemberBid{(*(this)).cmb_member_index,
                                (*(this)).cmb_new_force, (*(this)).cmb_side};
    }
  };

  __attribute__((pure)) static Coalition
  update_coalition_force(const List<CoalitionMember> &c,
                         const unsigned int &idx, List<Unit> new_force);

  struct ForceBid {
    Force bid_force;
    Side bid_side;
    Commander bid_commander;

    // ACCESSORS
    __attribute__((pure)) ForceBid clone() const {
      return ForceBid{(*(this)).bid_force, (*(this)).bid_side,
                      (*(this)).bid_commander.clone()};
    }
  };

  __attribute__((pure)) static ForceMetrics bid_metrics(const ForceBid &b);
  __attribute__((pure)) static std::optional<Commander>
  coalition_lead_commander(const List<CoalitionMember> &c);
  __attribute__((pure)) static std::optional<ForceBid>
  coalition_to_bid(const List<CoalitionMember> &c, const Side side);
  __attribute__((pure)) static Coalition
  apply_coalition_member_bid(const List<CoalitionMember> &c,
                             const CoalitionMemberBid &cbid);
  __attribute__((pure)) static bool
  valid_coalition_member_bid_b(const List<CoalitionMember> &c,
                               const CoalitionMemberBid &cbid);
  enum class TrialType { e_TRIALOFPOSSESSION, e_TRIALOFANNIHILATION };

  template <typename T1>
  static T1 TrialType_rect(const T1 f, const T1 f0, const TrialType t) {
    switch (t) {
    case TrialType::e_TRIALOFPOSSESSION: {
      return f;
    }
    case TrialType::e_TRIALOFANNIHILATION: {
      return f0;
    }
    default:
      std::unreachable();
    }
  }

  template <typename T1>
  static T1 TrialType_rec(const T1 f, const T1 f0, const TrialType t) {
    switch (t) {
    case TrialType::e_TRIALOFPOSSESSION: {
      return f;
    }
    case TrialType::e_TRIALOFANNIHILATION: {
      return f0;
    }
    default:
      std::unreachable();
    }
  }

  struct Prize {
    // TYPES
    struct PrizeHonor {};

    struct PrizeEnclave {
      unsigned int d_enclave_id;
    };

    using variant_t = std::variant<PrizeHonor, PrizeEnclave>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    Prize() {}

    explicit Prize(PrizeHonor _v) : d_v_(_v) {}

    explicit Prize(PrizeEnclave _v) : d_v_(std::move(_v)) {}

    Prize(const Prize &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    Prize(Prize &&_other) : d_v_(std::move(_other.d_v_)) {}

    Prize &operator=(const Prize &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    Prize &operator=(Prize &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) Prize clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<PrizeHonor>(_sv.v())) {
        return Prize(PrizeHonor{});
      } else {
        const auto &[d_enclave_id] = std::get<PrizeEnclave>(_sv.v());
        return Prize(PrizeEnclave{d_enclave_id});
      }
    }

    // CREATORS
    __attribute__((pure)) static Prize prizehonor() {
      return Prize(PrizeHonor{});
    }

    __attribute__((pure)) static Prize prizeenclave(unsigned int enclave_id) {
      return Prize(PrizeEnclave{std::move(enclave_id)});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    template <typename T1, MapsTo<T1, unsigned int> F1>
    T1 Prize_rec(const T1 f, F1 &&f0) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename Prize::PrizeHonor>(_sv.v())) {
        return f;
      } else {
        const auto &[d_enclave_id] =
            std::get<typename Prize::PrizeEnclave>(_sv.v());
        return f0(d_enclave_id);
      }
    }

    template <typename T1, MapsTo<T1, unsigned int> F1>
    T1 Prize_rect(const T1 f, F1 &&f0) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename Prize::PrizeHonor>(_sv.v())) {
        return f;
      } else {
        const auto &[d_enclave_id] =
            std::get<typename Prize::PrizeEnclave>(_sv.v());
        return f0(d_enclave_id);
      }
    }
  };

  struct Location {
    // TYPES
    struct LocPlanetSurface {
      unsigned int d_world_id;
      unsigned int d_region_id;
    };

    struct LocEnclave {
      unsigned int d_enclave_id;
    };

    using variant_t = std::variant<LocPlanetSurface, LocEnclave>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    Location() {}

    explicit Location(LocPlanetSurface _v) : d_v_(std::move(_v)) {}

    explicit Location(LocEnclave _v) : d_v_(std::move(_v)) {}

    Location(const Location &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    Location(Location &&_other) : d_v_(std::move(_other.d_v_)) {}

    Location &operator=(const Location &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    Location &operator=(Location &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) Location clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<LocPlanetSurface>(_sv.v())) {
        const auto &[d_world_id, d_region_id] =
            std::get<LocPlanetSurface>(_sv.v());
        return Location(LocPlanetSurface{d_world_id, d_region_id});
      } else {
        const auto &[d_enclave_id] = std::get<LocEnclave>(_sv.v());
        return Location(LocEnclave{d_enclave_id});
      }
    }

    // CREATORS
    __attribute__((pure)) static Location
    locplanetsurface(unsigned int world_id, unsigned int region_id) {
      return Location(
          LocPlanetSurface{std::move(world_id), std::move(region_id)});
    }

    __attribute__((pure)) static Location locenclave(unsigned int enclave_id) {
      return Location(LocEnclave{std::move(enclave_id)});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    template <typename T1, MapsTo<T1, unsigned int, unsigned int> F0,
              MapsTo<T1, unsigned int> F1>
    T1 Location_rec(F0 &&f, F1 &&f0) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename Location::LocPlanetSurface>(
              _sv.v())) {
        const auto &[d_world_id, d_region_id] =
            std::get<typename Location::LocPlanetSurface>(_sv.v());
        return f(d_world_id, d_region_id);
      } else {
        const auto &[d_enclave_id] =
            std::get<typename Location::LocEnclave>(_sv.v());
        return f0(d_enclave_id);
      }
    }

    template <typename T1, MapsTo<T1, unsigned int, unsigned int> F0,
              MapsTo<T1, unsigned int> F1>
    T1 Location_rect(F0 &&f, F1 &&f0) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename Location::LocPlanetSurface>(
              _sv.v())) {
        const auto &[d_world_id, d_region_id] =
            std::get<typename Location::LocPlanetSurface>(_sv.v());
        return f(d_world_id, d_region_id);
      } else {
        const auto &[d_enclave_id] =
            std::get<typename Location::LocEnclave>(_sv.v());
        return f0(d_enclave_id);
      }
    }
  };

  struct BattleContext {
    bool ctx_hegira_allowed;
    bool ctx_circle_present;

    // ACCESSORS
    __attribute__((pure)) BattleContext clone() const {
      return BattleContext{(*(this)).ctx_hegira_allowed,
                           (*(this)).ctx_circle_present};
    }
  };

  static inline const BattleContext standard_possession_context =
      BattleContext{true, false};

  struct BatchallChallenge {
    Commander chal_challenger;
    Clan chal_clan;
    Prize chal_prize;
    Force chal_initial_force;
    Location chal_location;
    TrialType chal_trial_type;
    BattleContext chal_context;

    // ACCESSORS
    __attribute__((pure)) BatchallChallenge clone() const {
      return BatchallChallenge{
          (*(this)).chal_challenger.clone(), (*(this)).chal_clan,
          (*(this)).chal_prize.clone(),      (*(this)).chal_initial_force,
          (*(this)).chal_location.clone(),   (*(this)).chal_trial_type,
          (*(this)).chal_context.clone()};
    }
  };

  struct BatchallResponse {
    Commander resp_defender;
    Clan resp_clan;
    Force resp_force;

    // ACCESSORS
    __attribute__((pure)) BatchallResponse clone() const {
      return BatchallResponse{(*(this)).resp_defender.clone(),
                              (*(this)).resp_clan, (*(this)).resp_force};
    }
  };

  struct RefusalReason {
    // TYPES
    struct RefusalInsufficientRank {};

    struct RefusalOther {
      unsigned int d_note;
    };

    using variant_t = std::variant<RefusalInsufficientRank, RefusalOther>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    RefusalReason() {}

    explicit RefusalReason(RefusalInsufficientRank _v) : d_v_(_v) {}

    explicit RefusalReason(RefusalOther _v) : d_v_(std::move(_v)) {}

    RefusalReason(const RefusalReason &_other)
        : d_v_(std::move(_other.clone().d_v_)) {}

    RefusalReason(RefusalReason &&_other) : d_v_(std::move(_other.d_v_)) {}

    RefusalReason &operator=(const RefusalReason &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    RefusalReason &operator=(RefusalReason &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) RefusalReason clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<RefusalInsufficientRank>(_sv.v())) {
        return RefusalReason(RefusalInsufficientRank{});
      } else {
        const auto &[d_note] = std::get<RefusalOther>(_sv.v());
        return RefusalReason(RefusalOther{d_note});
      }
    }

    // CREATORS
    __attribute__((pure)) static RefusalReason refusalinsufficientrank() {
      return RefusalReason(RefusalInsufficientRank{});
    }

    __attribute__((pure)) static RefusalReason refusalother(unsigned int note) {
      return RefusalReason(RefusalOther{std::move(note)});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    template <typename T1, MapsTo<T1, unsigned int> F1>
    T1 RefusalReason_rec(const T1 f, F1 &&f0) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<
              typename RefusalReason::RefusalInsufficientRank>(_sv.v())) {
        return f;
      } else {
        const auto &[d_note] =
            std::get<typename RefusalReason::RefusalOther>(_sv.v());
        return f0(d_note);
      }
    }

    template <typename T1, MapsTo<T1, unsigned int> F1>
    T1 RefusalReason_rect(const T1 f, F1 &&f0) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<
              typename RefusalReason::RefusalInsufficientRank>(_sv.v())) {
        return f;
      } else {
        const auto &[d_note] =
            std::get<typename RefusalReason::RefusalOther>(_sv.v());
        return f0(d_note);
      }
    }
  };

  struct ProtocolAction {
    // TYPES
    struct ActChallenge {
      BatchallChallenge d_chal;
    };

    struct ActRespond {
      BatchallResponse d_resp;
    };

    struct ActRefuse {
      RefusalReason d_reason;
    };

    struct ActBid {
      ForceBid d_bid;
    };

    struct ActCoalitionBid {
      CoalitionMemberBid d_cbid;
    };

    struct ActPass {
      Side d_side;
    };

    struct ActClose {};

    struct ActWithdraw {
      Side d_side;
    };

    struct ActBreakBid {
      Side d_side;
    };

    using variant_t = std::variant<ActChallenge, ActRespond, ActRefuse, ActBid,
                                   ActCoalitionBid, ActPass, ActClose,
                                   ActWithdraw, ActBreakBid>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    ProtocolAction() {}

    explicit ProtocolAction(ActChallenge _v) : d_v_(std::move(_v)) {}

    explicit ProtocolAction(ActRespond _v) : d_v_(std::move(_v)) {}

    explicit ProtocolAction(ActRefuse _v) : d_v_(std::move(_v)) {}

    explicit ProtocolAction(ActBid _v) : d_v_(std::move(_v)) {}

    explicit ProtocolAction(ActCoalitionBid _v) : d_v_(std::move(_v)) {}

    explicit ProtocolAction(ActPass _v) : d_v_(std::move(_v)) {}

    explicit ProtocolAction(ActClose _v) : d_v_(_v) {}

    explicit ProtocolAction(ActWithdraw _v) : d_v_(std::move(_v)) {}

    explicit ProtocolAction(ActBreakBid _v) : d_v_(std::move(_v)) {}

    ProtocolAction(const ProtocolAction &_other)
        : d_v_(std::move(_other.clone().d_v_)) {}

    ProtocolAction(ProtocolAction &&_other) : d_v_(std::move(_other.d_v_)) {}

    ProtocolAction &operator=(const ProtocolAction &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    ProtocolAction &operator=(ProtocolAction &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) ProtocolAction clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<ActChallenge>(_sv.v())) {
        const auto &[d_chal] = std::get<ActChallenge>(_sv.v());
        return ProtocolAction(ActChallenge{d_chal.clone()});
      } else if (std::holds_alternative<ActRespond>(_sv.v())) {
        const auto &[d_resp] = std::get<ActRespond>(_sv.v());
        return ProtocolAction(ActRespond{d_resp.clone()});
      } else if (std::holds_alternative<ActRefuse>(_sv.v())) {
        const auto &[d_reason] = std::get<ActRefuse>(_sv.v());
        return ProtocolAction(ActRefuse{d_reason.clone()});
      } else if (std::holds_alternative<ActBid>(_sv.v())) {
        const auto &[d_bid] = std::get<ActBid>(_sv.v());
        return ProtocolAction(ActBid{d_bid.clone()});
      } else if (std::holds_alternative<ActCoalitionBid>(_sv.v())) {
        const auto &[d_cbid] = std::get<ActCoalitionBid>(_sv.v());
        return ProtocolAction(ActCoalitionBid{d_cbid.clone()});
      } else if (std::holds_alternative<ActPass>(_sv.v())) {
        const auto &[d_side] = std::get<ActPass>(_sv.v());
        return ProtocolAction(ActPass{d_side});
      } else if (std::holds_alternative<ActClose>(_sv.v())) {
        return ProtocolAction(ActClose{});
      } else if (std::holds_alternative<ActWithdraw>(_sv.v())) {
        const auto &[d_side] = std::get<ActWithdraw>(_sv.v());
        return ProtocolAction(ActWithdraw{d_side});
      } else {
        const auto &[d_side] = std::get<ActBreakBid>(_sv.v());
        return ProtocolAction(ActBreakBid{d_side});
      }
    }

    // CREATORS
    __attribute__((pure)) static ProtocolAction
    actchallenge(BatchallChallenge chal) {
      return ProtocolAction(ActChallenge{std::move(chal)});
    }

    __attribute__((pure)) static ProtocolAction
    actrespond(BatchallResponse resp) {
      return ProtocolAction(ActRespond{std::move(resp)});
    }

    __attribute__((pure)) static ProtocolAction
    actrefuse(RefusalReason reason) {
      return ProtocolAction(ActRefuse{std::move(reason)});
    }

    __attribute__((pure)) static ProtocolAction actbid(ForceBid bid) {
      return ProtocolAction(ActBid{std::move(bid)});
    }

    __attribute__((pure)) static ProtocolAction
    actcoalitionbid(CoalitionMemberBid cbid) {
      return ProtocolAction(ActCoalitionBid{std::move(cbid)});
    }

    __attribute__((pure)) static ProtocolAction actpass(Side side) {
      return ProtocolAction(ActPass{std::move(side)});
    }

    __attribute__((pure)) static ProtocolAction actclose() {
      return ProtocolAction(ActClose{});
    }

    __attribute__((pure)) static ProtocolAction actwithdraw(Side side) {
      return ProtocolAction(ActWithdraw{std::move(side)});
    }

    __attribute__((pure)) static ProtocolAction actbreakbid(Side side) {
      return ProtocolAction(ActBreakBid{std::move(side)});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, BatchallChallenge> F0,
            MapsTo<T1, BatchallResponse> F1, MapsTo<T1, RefusalReason> F2,
            MapsTo<T1, ForceBid> F3, MapsTo<T1, CoalitionMemberBid> F4,
            MapsTo<T1, Side> F5, MapsTo<T1, Side> F7, MapsTo<T1, Side> F8>
  static T1 ProtocolAction_rect(F0 &&f, F1 &&f0, F2 &&f1, F3 &&f2, F4 &&f3,
                                F5 &&f4, const T1 f5, F7 &&f6, F8 &&f7,
                                const ProtocolAction &p) {
    if (std::holds_alternative<typename ProtocolAction::ActChallenge>(p.v())) {
      const auto &[d_chal] =
          std::get<typename ProtocolAction::ActChallenge>(p.v());
      return f(d_chal);
    } else if (std::holds_alternative<typename ProtocolAction::ActRespond>(
                   p.v())) {
      const auto &[d_resp] =
          std::get<typename ProtocolAction::ActRespond>(p.v());
      return f0(d_resp);
    } else if (std::holds_alternative<typename ProtocolAction::ActRefuse>(
                   p.v())) {
      const auto &[d_reason] =
          std::get<typename ProtocolAction::ActRefuse>(p.v());
      return f1(d_reason);
    } else if (std::holds_alternative<typename ProtocolAction::ActBid>(p.v())) {
      const auto &[d_bid] = std::get<typename ProtocolAction::ActBid>(p.v());
      return f2(d_bid);
    } else if (std::holds_alternative<typename ProtocolAction::ActCoalitionBid>(
                   p.v())) {
      const auto &[d_cbid] =
          std::get<typename ProtocolAction::ActCoalitionBid>(p.v());
      return f3(d_cbid);
    } else if (std::holds_alternative<typename ProtocolAction::ActPass>(
                   p.v())) {
      const auto &[d_side] = std::get<typename ProtocolAction::ActPass>(p.v());
      return f4(d_side);
    } else if (std::holds_alternative<typename ProtocolAction::ActClose>(
                   p.v())) {
      return f5;
    } else if (std::holds_alternative<typename ProtocolAction::ActWithdraw>(
                   p.v())) {
      const auto &[d_side] =
          std::get<typename ProtocolAction::ActWithdraw>(p.v());
      return f6(d_side);
    } else {
      const auto &[d_side] =
          std::get<typename ProtocolAction::ActBreakBid>(p.v());
      return f7(d_side);
    }
  }

  template <typename T1, MapsTo<T1, BatchallChallenge> F0,
            MapsTo<T1, BatchallResponse> F1, MapsTo<T1, RefusalReason> F2,
            MapsTo<T1, ForceBid> F3, MapsTo<T1, CoalitionMemberBid> F4,
            MapsTo<T1, Side> F5, MapsTo<T1, Side> F7, MapsTo<T1, Side> F8>
  static T1 ProtocolAction_rec(F0 &&f, F1 &&f0, F2 &&f1, F3 &&f2, F4 &&f3,
                               F5 &&f4, const T1 f5, F7 &&f6, F8 &&f7,
                               const ProtocolAction &p) {
    if (std::holds_alternative<typename ProtocolAction::ActChallenge>(p.v())) {
      const auto &[d_chal] =
          std::get<typename ProtocolAction::ActChallenge>(p.v());
      return f(d_chal);
    } else if (std::holds_alternative<typename ProtocolAction::ActRespond>(
                   p.v())) {
      const auto &[d_resp] =
          std::get<typename ProtocolAction::ActRespond>(p.v());
      return f0(d_resp);
    } else if (std::holds_alternative<typename ProtocolAction::ActRefuse>(
                   p.v())) {
      const auto &[d_reason] =
          std::get<typename ProtocolAction::ActRefuse>(p.v());
      return f1(d_reason);
    } else if (std::holds_alternative<typename ProtocolAction::ActBid>(p.v())) {
      const auto &[d_bid] = std::get<typename ProtocolAction::ActBid>(p.v());
      return f2(d_bid);
    } else if (std::holds_alternative<typename ProtocolAction::ActCoalitionBid>(
                   p.v())) {
      const auto &[d_cbid] =
          std::get<typename ProtocolAction::ActCoalitionBid>(p.v());
      return f3(d_cbid);
    } else if (std::holds_alternative<typename ProtocolAction::ActPass>(
                   p.v())) {
      const auto &[d_side] = std::get<typename ProtocolAction::ActPass>(p.v());
      return f4(d_side);
    } else if (std::holds_alternative<typename ProtocolAction::ActClose>(
                   p.v())) {
      return f5;
    } else if (std::holds_alternative<typename ProtocolAction::ActWithdraw>(
                   p.v())) {
      const auto &[d_side] =
          std::get<typename ProtocolAction::ActWithdraw>(p.v());
      return f6(d_side);
    } else {
      const auto &[d_side] =
          std::get<typename ProtocolAction::ActBreakBid>(p.v());
      return f7(d_side);
    }
  }
  enum class ReadyStatus {
    e_NEITHERREADY,
    e_ATTACKERREADY,
    e_DEFENDERREADY,
    e_BOTHREADY
  };

  template <typename T1>
  static T1 ReadyStatus_rect(const T1 f, const T1 f0, const T1 f1, const T1 f2,
                             const ReadyStatus r) {
    switch (r) {
    case ReadyStatus::e_NEITHERREADY: {
      return f;
    }
    case ReadyStatus::e_ATTACKERREADY: {
      return f0;
    }
    case ReadyStatus::e_DEFENDERREADY: {
      return f1;
    }
    case ReadyStatus::e_BOTHREADY: {
      return f2;
    }
    default:
      std::unreachable();
    }
  }

  template <typename T1>
  static T1 ReadyStatus_rec(const T1 f, const T1 f0, const T1 f1, const T1 f2,
                            const ReadyStatus r) {
    switch (r) {
    case ReadyStatus::e_NEITHERREADY: {
      return f;
    }
    case ReadyStatus::e_ATTACKERREADY: {
      return f0;
    }
    case ReadyStatus::e_DEFENDERREADY: {
      return f1;
    }
    case ReadyStatus::e_BOTHREADY: {
      return f2;
    }
    default:
      std::unreachable();
    }
  }

  __attribute__((pure)) static bool is_ready(const ReadyStatus rs,
                                             const Side side);
  __attribute__((pure)) static ReadyStatus set_ready(const ReadyStatus rs,
                                                     const Side side);
  __attribute__((pure)) static ReadyStatus clear_ready(const ReadyStatus rs,
                                                       const Side side);
  using CoalitionState = std::optional<Coalition>;
  __attribute__((pure)) static Force
  coalition_state_force(const std::optional<List<CoalitionMember>> &cs,
                        List<Unit> fallback);

  struct BatchallPhase {
    // TYPES
    struct PhaseIdle {};

    struct PhaseChallenged {
      BatchallChallenge d_challenge;
    };

    struct PhaseResponded {
      BatchallChallenge d_challenge;
      BatchallResponse d_response;
    };

    struct PhaseBidding {
      BatchallChallenge d_challenge;
      BatchallResponse d_response;
      ForceBid d_attacker_bid;
      ForceBid d_defender_bid;
      CoalitionState d_attacker_coalition;
      CoalitionState d_defender_coalition;
      List<ForceBid> d_bid_history;
      ReadyStatus d_ready;
    };

    struct PhaseAgreed {
      BatchallChallenge d_challenge;
      BatchallResponse d_response;
      ForceBid d_final_attacker;
      ForceBid d_final_defender;
    };

    struct PhaseRefused {
      BatchallChallenge d_challenge;
      RefusalReason d_reason;
    };

    struct PhaseAborted {
      ProtocolAction d_reason;
    };

    using variant_t =
        std::variant<PhaseIdle, PhaseChallenged, PhaseResponded, PhaseBidding,
                     PhaseAgreed, PhaseRefused, PhaseAborted>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    BatchallPhase() {}

    explicit BatchallPhase(PhaseIdle _v) : d_v_(_v) {}

    explicit BatchallPhase(PhaseChallenged _v) : d_v_(std::move(_v)) {}

    explicit BatchallPhase(PhaseResponded _v) : d_v_(std::move(_v)) {}

    explicit BatchallPhase(PhaseBidding _v) : d_v_(std::move(_v)) {}

    explicit BatchallPhase(PhaseAgreed _v) : d_v_(std::move(_v)) {}

    explicit BatchallPhase(PhaseRefused _v) : d_v_(std::move(_v)) {}

    explicit BatchallPhase(PhaseAborted _v) : d_v_(std::move(_v)) {}

    BatchallPhase(const BatchallPhase &_other)
        : d_v_(std::move(_other.clone().d_v_)) {}

    BatchallPhase(BatchallPhase &&_other) : d_v_(std::move(_other.d_v_)) {}

    BatchallPhase &operator=(const BatchallPhase &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    BatchallPhase &operator=(BatchallPhase &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) BatchallPhase clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<PhaseIdle>(_sv.v())) {
        return BatchallPhase(PhaseIdle{});
      } else if (std::holds_alternative<PhaseChallenged>(_sv.v())) {
        const auto &[d_challenge] = std::get<PhaseChallenged>(_sv.v());
        return BatchallPhase(PhaseChallenged{d_challenge.clone()});
      } else if (std::holds_alternative<PhaseResponded>(_sv.v())) {
        const auto &[d_challenge, d_response] =
            std::get<PhaseResponded>(_sv.v());
        return BatchallPhase(
            PhaseResponded{d_challenge.clone(), d_response.clone()});
      } else if (std::holds_alternative<PhaseBidding>(_sv.v())) {
        const auto &[d_challenge, d_response, d_attacker_bid, d_defender_bid,
                     d_attacker_coalition, d_defender_coalition, d_bid_history,
                     d_ready] = std::get<PhaseBidding>(_sv.v());
        return BatchallPhase(PhaseBidding{
            d_challenge.clone(), d_response.clone(), d_attacker_bid.clone(),
            d_defender_bid.clone(), d_attacker_coalition, d_defender_coalition,
            d_bid_history.clone(), d_ready});
      } else if (std::holds_alternative<PhaseAgreed>(_sv.v())) {
        const auto &[d_challenge, d_response, d_final_attacker,
                     d_final_defender] = std::get<PhaseAgreed>(_sv.v());
        return BatchallPhase(
            PhaseAgreed{d_challenge.clone(), d_response.clone(),
                        d_final_attacker.clone(), d_final_defender.clone()});
      } else if (std::holds_alternative<PhaseRefused>(_sv.v())) {
        const auto &[d_challenge, d_reason] = std::get<PhaseRefused>(_sv.v());
        return BatchallPhase(
            PhaseRefused{d_challenge.clone(), d_reason.clone()});
      } else {
        const auto &[d_reason] = std::get<PhaseAborted>(_sv.v());
        return BatchallPhase(PhaseAborted{d_reason.clone()});
      }
    }

    // CREATORS
    __attribute__((pure)) static BatchallPhase phaseidle() {
      return BatchallPhase(PhaseIdle{});
    }

    __attribute__((pure)) static BatchallPhase
    phasechallenged(BatchallChallenge challenge) {
      return BatchallPhase(PhaseChallenged{std::move(challenge)});
    }

    __attribute__((pure)) static BatchallPhase
    phaseresponded(BatchallChallenge challenge, BatchallResponse response) {
      return BatchallPhase(
          PhaseResponded{std::move(challenge), std::move(response)});
    }

    __attribute__((pure)) static BatchallPhase
    phasebidding(BatchallChallenge challenge, BatchallResponse response,
                 ForceBid attacker_bid, ForceBid defender_bid,
                 CoalitionState attacker_coalition,
                 CoalitionState defender_coalition, List<ForceBid> bid_history,
                 ReadyStatus ready) {
      return BatchallPhase(PhaseBidding{
          std::move(challenge), std::move(response), std::move(attacker_bid),
          std::move(defender_bid), std::move(attacker_coalition),
          std::move(defender_coalition), std::move(bid_history),
          std::move(ready)});
    }

    __attribute__((pure)) static BatchallPhase
    phaseagreed(BatchallChallenge challenge, BatchallResponse response,
                ForceBid final_attacker, ForceBid final_defender) {
      return BatchallPhase(
          PhaseAgreed{std::move(challenge), std::move(response),
                      std::move(final_attacker), std::move(final_defender)});
    }

    __attribute__((pure)) static BatchallPhase
    phaserefused(BatchallChallenge challenge, RefusalReason reason) {
      return BatchallPhase(
          PhaseRefused{std::move(challenge), std::move(reason)});
    }

    __attribute__((pure)) static BatchallPhase
    phaseaborted(ProtocolAction reason) {
      return BatchallPhase(PhaseAborted{std::move(reason)});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    __attribute__((pure)) std::optional<Commander>
    action_actor_in_phase(const ProtocolAction &action) const {
      if (std::holds_alternative<typename ProtocolAction::ActChallenge>(
              action.v())) {
        const auto &[d_chal] =
            std::get<typename ProtocolAction::ActChallenge>(action.v());
        return std::make_optional<Commander>(d_chal.chal_challenger);
      } else if (std::holds_alternative<typename ProtocolAction::ActRespond>(
                     action.v())) {
        const auto &[d_resp] =
            std::get<typename ProtocolAction::ActRespond>(action.v());
        return std::make_optional<Commander>(d_resp.resp_defender);
      } else if (std::holds_alternative<typename ProtocolAction::ActBid>(
                     action.v())) {
        const auto &[d_bid] =
            std::get<typename ProtocolAction::ActBid>(action.v());
        return std::make_optional<Commander>(d_bid.bid_commander);
      } else if (std::holds_alternative<typename ProtocolAction::ActWithdraw>(
                     action.v())) {
        const auto &[d_side] =
            std::get<typename ProtocolAction::ActWithdraw>(action.v());
        return (*(this)).get_side_commander(d_side);
      } else if (std::holds_alternative<typename ProtocolAction::ActBreakBid>(
                     action.v())) {
        const auto &[d_side] =
            std::get<typename ProtocolAction::ActBreakBid>(action.v());
        return (*(this)).get_side_commander(d_side);
      } else {
        return std::optional<Commander>();
      }
    }

    __attribute__((pure)) std::optional<Commander>
    get_side_commander(const Side side) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename BatchallPhase::PhaseBidding>(
              _sv.v())) {
        const auto &[d_challenge, d_response, d_attacker_bid, d_defender_bid,
                     d_attacker_coalition, d_defender_coalition, d_bid_history,
                     d_ready] =
            std::get<typename BatchallPhase::PhaseBidding>(_sv.v());
        switch (side) {
        case Side::e_ATTACKER: {
          return std::make_optional<Commander>(d_attacker_bid.bid_commander);
        }
        case Side::e_DEFENDER: {
          return std::make_optional<Commander>(d_defender_bid.bid_commander);
        }
        default:
          std::unreachable();
        }
      } else {
        return std::optional<Commander>();
      }
    }

    __attribute__((pure)) unsigned int get_bidding_measure() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename BatchallPhase::PhaseBidding>(
              _sv.v())) {
        const auto &[d_challenge, d_response, d_attacker_bid, d_defender_bid,
                     d_attacker_coalition, d_defender_coalition, d_bid_history,
                     d_ready] =
            std::get<typename BatchallPhase::PhaseBidding>(_sv.v());
        return ((bid_metrics(d_attacker_bid).fm_total_ecr +
                 bid_metrics(d_defender_bid).fm_total_ecr) +
                [&]() {
                  switch (d_ready) {
                  case ReadyStatus::e_NEITHERREADY: {
                    return 2u;
                  }
                  case ReadyStatus::e_BOTHREADY: {
                    return 0u;
                  }
                  default: {
                    return 1u;
                  }
                  }
                }());
      } else {
        return 0u;
      }
    }

    __attribute__((pure)) unsigned int phase_depth() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename BatchallPhase::PhaseIdle>(_sv.v())) {
        return 4u;
      } else if (std::holds_alternative<
                     typename BatchallPhase::PhaseChallenged>(_sv.v())) {
        return 3u;
      } else if (std::holds_alternative<typename BatchallPhase::PhaseResponded>(
                     _sv.v())) {
        return 2u;
      } else if (std::holds_alternative<typename BatchallPhase::PhaseBidding>(
                     _sv.v())) {
        return 1u;
      } else {
        return 0u;
      }
    }

    __attribute__((pure)) bool is_bidding() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename BatchallPhase::PhaseBidding>(
              _sv.v())) {
        return true;
      } else {
        return false;
      }
    }

    __attribute__((pure)) bool is_terminal() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename BatchallPhase::PhaseAgreed>(
              _sv.v())) {
        return true;
      } else if (std::holds_alternative<typename BatchallPhase::PhaseRefused>(
                     _sv.v())) {
        return true;
      } else if (std::holds_alternative<typename BatchallPhase::PhaseAborted>(
                     _sv.v())) {
        return true;
      } else {
        return false;
      }
    }
  };

  template <
      typename T1, MapsTo<T1, BatchallChallenge> F1,
      MapsTo<T1, BatchallChallenge, BatchallResponse> F2,
      MapsTo<T1, BatchallChallenge, BatchallResponse, ForceBid, ForceBid,
             std::optional<List<CoalitionMember>>,
             std::optional<List<CoalitionMember>>, List<ForceBid>, ReadyStatus>
          F3,
      MapsTo<T1, BatchallChallenge, BatchallResponse, ForceBid, ForceBid> F4,
      MapsTo<T1, BatchallChallenge, RefusalReason> F5,
      MapsTo<T1, ProtocolAction> F6>
  static T1 BatchallPhase_rect(const T1 f, F1 &&f0, F2 &&f1, F3 &&f2, F4 &&f3,
                               F5 &&f4, F6 &&f5, const BatchallPhase &b) {
    if (std::holds_alternative<typename BatchallPhase::PhaseIdle>(b.v())) {
      return f;
    } else if (std::holds_alternative<typename BatchallPhase::PhaseChallenged>(
                   b.v())) {
      const auto &[d_challenge] =
          std::get<typename BatchallPhase::PhaseChallenged>(b.v());
      return f0(d_challenge);
    } else if (std::holds_alternative<typename BatchallPhase::PhaseResponded>(
                   b.v())) {
      const auto &[d_challenge, d_response] =
          std::get<typename BatchallPhase::PhaseResponded>(b.v());
      return f1(d_challenge, d_response);
    } else if (std::holds_alternative<typename BatchallPhase::PhaseBidding>(
                   b.v())) {
      const auto &[d_challenge, d_response, d_attacker_bid, d_defender_bid,
                   d_attacker_coalition, d_defender_coalition, d_bid_history,
                   d_ready] =
          std::get<typename BatchallPhase::PhaseBidding>(b.v());
      return f2(d_challenge, d_response, d_attacker_bid, d_defender_bid,
                d_attacker_coalition, d_defender_coalition, d_bid_history,
                d_ready);
    } else if (std::holds_alternative<typename BatchallPhase::PhaseAgreed>(
                   b.v())) {
      const auto &[d_challenge, d_response, d_final_attacker,
                   d_final_defender] =
          std::get<typename BatchallPhase::PhaseAgreed>(b.v());
      return f3(d_challenge, d_response, d_final_attacker, d_final_defender);
    } else if (std::holds_alternative<typename BatchallPhase::PhaseRefused>(
                   b.v())) {
      const auto &[d_challenge, d_reason] =
          std::get<typename BatchallPhase::PhaseRefused>(b.v());
      return f4(d_challenge, d_reason);
    } else {
      const auto &[d_reason] =
          std::get<typename BatchallPhase::PhaseAborted>(b.v());
      return f5(d_reason);
    }
  }

  template <
      typename T1, MapsTo<T1, BatchallChallenge> F1,
      MapsTo<T1, BatchallChallenge, BatchallResponse> F2,
      MapsTo<T1, BatchallChallenge, BatchallResponse, ForceBid, ForceBid,
             std::optional<List<CoalitionMember>>,
             std::optional<List<CoalitionMember>>, List<ForceBid>, ReadyStatus>
          F3,
      MapsTo<T1, BatchallChallenge, BatchallResponse, ForceBid, ForceBid> F4,
      MapsTo<T1, BatchallChallenge, RefusalReason> F5,
      MapsTo<T1, ProtocolAction> F6>
  static T1 BatchallPhase_rec(const T1 f, F1 &&f0, F2 &&f1, F3 &&f2, F4 &&f3,
                              F5 &&f4, F6 &&f5, const BatchallPhase &b) {
    if (std::holds_alternative<typename BatchallPhase::PhaseIdle>(b.v())) {
      return f;
    } else if (std::holds_alternative<typename BatchallPhase::PhaseChallenged>(
                   b.v())) {
      const auto &[d_challenge] =
          std::get<typename BatchallPhase::PhaseChallenged>(b.v());
      return f0(d_challenge);
    } else if (std::holds_alternative<typename BatchallPhase::PhaseResponded>(
                   b.v())) {
      const auto &[d_challenge, d_response] =
          std::get<typename BatchallPhase::PhaseResponded>(b.v());
      return f1(d_challenge, d_response);
    } else if (std::holds_alternative<typename BatchallPhase::PhaseBidding>(
                   b.v())) {
      const auto &[d_challenge, d_response, d_attacker_bid, d_defender_bid,
                   d_attacker_coalition, d_defender_coalition, d_bid_history,
                   d_ready] =
          std::get<typename BatchallPhase::PhaseBidding>(b.v());
      return f2(d_challenge, d_response, d_attacker_bid, d_defender_bid,
                d_attacker_coalition, d_defender_coalition, d_bid_history,
                d_ready);
    } else if (std::holds_alternative<typename BatchallPhase::PhaseAgreed>(
                   b.v())) {
      const auto &[d_challenge, d_response, d_final_attacker,
                   d_final_defender] =
          std::get<typename BatchallPhase::PhaseAgreed>(b.v());
      return f3(d_challenge, d_response, d_final_attacker, d_final_defender);
    } else if (std::holds_alternative<typename BatchallPhase::PhaseRefused>(
                   b.v())) {
      const auto &[d_challenge, d_reason] =
          std::get<typename BatchallPhase::PhaseRefused>(b.v());
      return f4(d_challenge, d_reason);
    } else {
      const auto &[d_reason] =
          std::get<typename BatchallPhase::PhaseAborted>(b.v());
      return f5(d_reason);
    }
  }

  using Honor = Z;
  using HonorEntry = std::pair<unsigned int, Honor>;
  using HonorLedger = List<HonorEntry>;
  __attribute__((pure)) static Honor
  ledger_lookup(const List<std::pair<unsigned int, Z>> &ledger,
                const unsigned int &warrior_id);
  __attribute__((pure)) static HonorLedger
  ledger_update_by_id(const List<std::pair<unsigned int, Z>> &ledger,
                      unsigned int warrior_id, Z new_honor);
  __attribute__((pure)) static HonorLedger
  update_honor(const List<std::pair<unsigned int, Z>> &ledger,
               const Commander &actor, const Z &delta);
  __attribute__((pure)) static Honor
  refusal_honor_delta(const RefusalReason &r);
  __attribute__((pure)) static Honor
  protocol_honor_delta(const ProtocolAction &action);

  struct BatchallState {
    BatchallPhase bs_phase;
    HonorLedger bs_honor;

    // ACCESSORS
    __attribute__((pure)) BatchallState clone() const {
      return BatchallState{(*(this)).bs_phase.clone(), (*(this)).bs_honor};
    }
  };

  static inline const HonorLedger empty_ledger =
      List<std::pair<unsigned int, Z>>::nil();
  static inline const BatchallState initial_state =
      BatchallState{BatchallPhase::phaseidle(), empty_ledger};
  __attribute__((pure)) static HonorLedger
  apply_action_honor(const BatchallState &state, const ProtocolAction &action);
  static inline const Commander malthus =
      Commander{1u, Clan::e_CLANJADEFALCON, Rank::e_STARCOLONEL, true};
  static inline const Commander radick =
      Commander{2u, Clan::e_CLANWOLF, Rank::e_STARCAPTAIN, true};
  static inline const Commander bear_ally =
      Commander{3u, Clan::e_CLANGHOSTBEAR, Rank::e_STARCAPTAIN, false};
  static inline const Unit timberwolf =
      Unit{101u, UnitClass::e_OMNIMECH, WeightClass::e_HEAVY, 75u, 2u, 3u, true,
           true};
  static inline const Unit direwolf = Unit{
      102u, UnitClass::e_OMNIMECH, WeightClass::e_ASSAULT, 100u, 2u, 3u, true,
      true};
  static inline const Unit summoner = Unit{
      103u, UnitClass::e_OMNIMECH, WeightClass::e_HEAVY, 70u, 3u, 4u, false,
      true};
  static inline const Unit mad_dog = Unit{
      104u, UnitClass::e_OMNIMECH, WeightClass::e_HEAVY, 60u, 3u, 4u, false,
      true};
  static inline const Unit elementals = Unit{
      105u, UnitClass::e_ELEMENTAL, WeightClass::e_LIGHT, 5u, 3u, 4u, false,
      true};
  static inline const Force falcon_trinary = List<Unit>::cons(
      direwolf,
      List<Unit>::cons(
          timberwolf,
          List<Unit>::cons(summoner,
                           List<Unit>::cons(mad_dog, List<Unit>::nil()))));
  static inline const Force wolf_binary = List<Unit>::cons(
      timberwolf, List<Unit>::cons(summoner, List<Unit>::nil()));
  static inline const Force bear_support = List<Unit>::cons(
      elementals, List<Unit>::cons(elementals, List<Unit>::nil()));
  static inline const Coalition attacker_coalition =
      List<CoalitionMember>::cons(
          CoalitionMember{Clan::e_CLANJADEFALCON, malthus, falcon_trinary},
          List<CoalitionMember>::cons(
              CoalitionMember{Clan::e_CLANGHOSTBEAR, bear_ally, bear_support},
              List<CoalitionMember>::nil()));
  static inline const Coalition defender_coalition =
      List<CoalitionMember>::cons(
          CoalitionMember{Clan::e_CLANWOLF, radick, wolf_binary},
          List<CoalitionMember>::nil());
  static inline const BatchallChallenge sample_challenge =
      BatchallChallenge{malthus,
                        Clan::e_CLANJADEFALCON,
                        Prize::prizeenclave(42u),
                        coalition_force(attacker_coalition),
                        Location::locplanetsurface(7u, 3u),
                        TrialType::e_TRIALOFPOSSESSION,
                        standard_possession_context};
  static inline const BatchallResponse sample_response = BatchallResponse{
      radick, Clan::e_CLANWOLF, coalition_force(defender_coalition)};
  static inline const ForceBid sample_attacker_bid = []() -> ForceBid {
    auto _cs = coalition_to_bid(attacker_coalition, Side::e_ATTACKER);
    if (_cs.has_value()) {
      const ForceBid &bid = *_cs;
      return bid;
    } else {
      return ForceBid{List<Unit>::nil(), Side::e_ATTACKER, malthus};
    }
  }();
  static inline const ForceBid sample_defender_bid = []() -> ForceBid {
    auto _cs = coalition_to_bid(defender_coalition, Side::e_DEFENDER);
    if (_cs.has_value()) {
      const ForceBid &bid = *_cs;
      return bid;
    } else {
      return ForceBid{List<Unit>::nil(), Side::e_DEFENDER, radick};
    }
  }();
  static inline const Force reduced_support_force =
      List<Unit>::cons(elementals, List<Unit>::nil());
  static inline const CoalitionMemberBid sample_coalition_member_bid =
      CoalitionMemberBid{1u, reduced_support_force, Side::e_ATTACKER};
  static inline const Coalition updated_attacker_coalition =
      apply_coalition_member_bid(attacker_coalition,
                                 sample_coalition_member_bid);
  static inline const ForceBid updated_attacker_bid = []() -> ForceBid {
    auto _cs = coalition_to_bid(updated_attacker_coalition, Side::e_ATTACKER);
    if (_cs.has_value()) {
      const ForceBid &bid = *_cs;
      return bid;
    } else {
      return sample_attacker_bid;
    }
  }();
  static inline const BatchallPhase phase_after_initial_bid =
      BatchallPhase::phasebidding(
          sample_challenge, sample_response, sample_attacker_bid,
          sample_defender_bid,
          std::make_optional<List<CoalitionMember>>(attacker_coalition),
          std::make_optional<List<CoalitionMember>>(defender_coalition),
          List<ForceBid>::nil(), ReadyStatus::e_NEITHERREADY);
  static inline const BatchallPhase phase_after_attacker_pass =
      BatchallPhase::phasebidding(
          sample_challenge, sample_response, sample_attacker_bid,
          sample_defender_bid,
          std::make_optional<List<CoalitionMember>>(attacker_coalition),
          std::make_optional<List<CoalitionMember>>(defender_coalition),
          List<ForceBid>::nil(), ReadyStatus::e_ATTACKERREADY);
  static inline const BatchallPhase phase_after_coalition_bid =
      BatchallPhase::phasebidding(
          sample_challenge, sample_response, updated_attacker_bid,
          sample_defender_bid,
          std::make_optional<List<CoalitionMember>>(updated_attacker_coalition),
          std::make_optional<List<CoalitionMember>>(defender_coalition),
          List<ForceBid>::cons(sample_attacker_bid, List<ForceBid>::nil()),
          ReadyStatus::e_NEITHERREADY);
  static inline const BatchallPhase phase_agreed =
      BatchallPhase::phaseagreed(sample_challenge, sample_response,
                                 updated_attacker_bid, sample_defender_bid);
  static inline const BatchallState state_after_initial_bid =
      BatchallState{phase_after_initial_bid, empty_ledger};
  static inline const HonorLedger sample_challenge_honor_ledger =
      apply_action_honor(initial_state,
                         ProtocolAction::actchallenge(sample_challenge));
  static inline const HonorLedger sample_break_bid_honor_ledger =
      apply_action_honor(state_after_initial_bid,
                         ProtocolAction::actbreakbid(Side::e_ATTACKER));
  static inline const bool sample_challenger_may_issue =
      may_issue_batchall(malthus);
  static inline const bool sample_coalition_bid_is_valid =
      valid_coalition_member_bid_b(attacker_coalition,
                                   sample_coalition_member_bid);
  static inline const bool sample_coalition_contains_bear =
      coalition_contains_clan(attacker_coalition, Clan::e_CLANGHOSTBEAR);
  static inline const bool sample_updated_tonnage_reduced =
      coalition_tonnage(updated_attacker_coalition) <
      coalition_tonnage(attacker_coalition);
  static inline const bool sample_attacker_ready_after_pass =
      is_ready(set_ready(ReadyStatus::e_NEITHERREADY, Side::e_ATTACKER),
               Side::e_ATTACKER);
  static inline const bool sample_attacker_not_ready_after_clear =
      !(is_ready(clear_ready(ReadyStatus::e_BOTHREADY, Side::e_ATTACKER),
                 Side::e_ATTACKER));
  static inline const bool sample_phase_is_bidding =
      phase_after_initial_bid.is_bidding();
  static inline const bool sample_agreed_terminal = phase_agreed.is_terminal();
  static inline const unsigned int sample_phase_depth_before_close =
      phase_after_initial_bid.phase_depth();
  static inline const unsigned int sample_phase_depth_after_close =
      phase_agreed.phase_depth();
  static inline const bool sample_bidding_measure_reduced =
      phase_after_coalition_bid.get_bidding_measure() <
      phase_after_initial_bid.get_bidding_measure();
  static inline const Honor sample_challenge_honor =
      ledger_lookup(sample_challenge_honor_ledger, malthus.cmd_id);
  static inline const Honor sample_break_bid_honor =
      ledger_lookup(sample_break_bid_honor_ledger, malthus.cmd_id);
  static inline const bool sample_challenge_honor_is_one =
      BinInt::eqb(sample_challenge_honor, Z::zpos(Positive::xh()));
  static inline const bool sample_break_bid_honor_is_minus_ten = BinInt::eqb(
      sample_break_bid_honor,
      Z::zneg(Positive::xo(Positive::xi(Positive::xo(Positive::xh())))));
  static inline const unsigned int sample_break_bid_actor_id =
      []() -> unsigned int {
    auto _cs = phase_after_initial_bid.action_actor_in_phase(
        ProtocolAction::actbreakbid(Side::e_ATTACKER));
    if (_cs.has_value()) {
      const Commander &cmd = *_cs;
      return cmd.cmd_id;
    } else {
      return 0u;
    }
  }();
  static inline const unsigned int sample_attacker_bid_count =
      bid_metrics(sample_attacker_bid).fm_count;
  static inline const unsigned int sample_updated_bid_count =
      bid_metrics(updated_attacker_bid).fm_count;
  static inline const unsigned int sample_state_force_count =
      coalition_state_force(
          std::make_optional<List<CoalitionMember>>(attacker_coalition),
          List<Unit>::nil())
          .length();
};

template <typename T1>
T1 ListDef::nth(const unsigned int &n, const List<T1> &l, const T1 default0) {
  if (n <= 0) {
    if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
      return default0;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<T1>::Cons>(l.v());
      return d_a0;
    }
  } else {
    unsigned int m = n - 1;
    if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
      return default0;
    } else {
      const auto &[d_a00, d_a10] = std::get<typename List<T1>::Cons>(l.v());
      return ListDef::template nth<T1>(m, *(d_a10), default0);
    }
  }
}

#endif // INCLUDED_COALITION_BID_HONOR_TRACE
