#ifndef INCLUDED_COALITION_BID_HONOR_TRACE
#define INCLUDED_COALITION_BID_HONOR_TRACE

#include <memory>
#include <optional>
#include <type_traits>
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

public:
  // CREATORS
  explicit List(Nil _v) : d_v_(_v) {}

  explicit List(Cons _v) : d_v_(std::move(_v)) {}

  static std::shared_ptr<List<t_A>> nil() {
    return std::make_shared<List<t_A>>(Nil{});
  }

  static std::shared_ptr<List<t_A>> cons(t_A a0,
                                         const std::shared_ptr<List<t_A>> &a1) {
    return std::make_shared<List<t_A>>(Cons{std::move(a0), a1});
  }

  static std::shared_ptr<List<t_A>> cons(t_A a0,
                                         std::shared_ptr<List<t_A>> &&a1) {
    return std::make_shared<List<t_A>>(Cons{std::move(a0), std::move(a1)});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }

  template <MapsTo<bool, t_A> F0>
  __attribute__((pure)) bool existsb(F0 &&f) const {
    if (std::holds_alternative<typename List<t_A>::Nil>(this->v())) {
      return false;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<t_A>::Cons>(this->v());
      return (f(d_a0) || d_a1->existsb(f));
    }
  }

  template <typename T1, MapsTo<T1, t_A, T1> F0>
  T1 fold_right(F0 &&f, const T1 a0) const {
    if (std::holds_alternative<typename List<t_A>::Nil>(this->v())) {
      return a0;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<t_A>::Cons>(this->v());
      return f(d_a0, d_a1->template fold_right<T1>(f, a0));
    }
  }

  template <typename T1, MapsTo<std::shared_ptr<List<T1>>, t_A> F0>
  std::shared_ptr<List<T1>> flat_map(F0 &&f) const {
    if (std::holds_alternative<typename List<t_A>::Nil>(this->v())) {
      return List<T1>::nil();
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<t_A>::Cons>(this->v());
      return f(d_a0)->app(d_a1->template flat_map<T1>(f));
    }
  }

  template <typename T1, MapsTo<T1, t_A> F0>
  std::shared_ptr<List<T1>> map(F0 &&f) const {
    if (std::holds_alternative<typename List<t_A>::Nil>(this->v())) {
      return List<T1>::nil();
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<t_A>::Cons>(this->v());
      return List<T1>::cons(f(d_a0), d_a1->template map<T1>(f));
    }
  }

  __attribute__((pure)) unsigned int length() const {
    if (std::holds_alternative<typename List<t_A>::Nil>(this->v())) {
      return 0u;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<t_A>::Cons>(this->v());
      return (d_a1->length() + 1);
    }
  }

  std::shared_ptr<List<t_A>> app(std::shared_ptr<List<t_A>> m) const {
    if (std::holds_alternative<typename List<t_A>::Nil>(this->v())) {
      return m;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<t_A>::Cons>(this->v());
      return List<t_A>::cons(d_a0, d_a1->app(m));
    }
  }
};

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

public:
  // CREATORS
  explicit Positive(XI _v) : d_v_(std::move(_v)) {}

  explicit Positive(XO _v) : d_v_(std::move(_v)) {}

  explicit Positive(XH _v) : d_v_(_v) {}

  static std::shared_ptr<Positive> xi(const std::shared_ptr<Positive> &a0) {
    return std::make_shared<Positive>(XI{a0});
  }

  static std::shared_ptr<Positive> xi(std::shared_ptr<Positive> &&a0) {
    return std::make_shared<Positive>(XI{std::move(a0)});
  }

  static std::shared_ptr<Positive> xo(const std::shared_ptr<Positive> &a0) {
    return std::make_shared<Positive>(XO{a0});
  }

  static std::shared_ptr<Positive> xo(std::shared_ptr<Positive> &&a0) {
    return std::make_shared<Positive>(XO{std::move(a0)});
  }

  static std::shared_ptr<Positive> xh() {
    return std::make_shared<Positive>(XH{});
  }

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

public:
  // CREATORS
  explicit Z(Z0 _v) : d_v_(_v) {}

  explicit Z(Zpos _v) : d_v_(std::move(_v)) {}

  explicit Z(Zneg _v) : d_v_(std::move(_v)) {}

  static std::shared_ptr<Z> z0() { return std::make_shared<Z>(Z0{}); }

  static std::shared_ptr<Z> zpos(const std::shared_ptr<Positive> &a0) {
    return std::make_shared<Z>(Zpos{a0});
  }

  static std::shared_ptr<Z> zpos(std::shared_ptr<Positive> &&a0) {
    return std::make_shared<Z>(Zpos{std::move(a0)});
  }

  static std::shared_ptr<Z> zneg(const std::shared_ptr<Positive> &a0) {
    return std::make_shared<Z>(Zneg{a0});
  }

  static std::shared_ptr<Z> zneg(std::shared_ptr<Positive> &&a0) {
    return std::make_shared<Z>(Zneg{std::move(a0)});
  }

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
  __attribute__((pure)) static bool eqb(const std::shared_ptr<Positive> &p,
                                        const std::shared_ptr<Positive> &q);
};

struct BinInt {
  static std::shared_ptr<Z> double_(const std::shared_ptr<Z> &x);
  static std::shared_ptr<Z> succ_double(const std::shared_ptr<Z> &x);
  static std::shared_ptr<Z> pred_double(const std::shared_ptr<Z> &x);
  static std::shared_ptr<Z> pos_sub(const std::shared_ptr<Positive> &x,
                                    const std::shared_ptr<Positive> &y);
  static std::shared_ptr<Z> add(std::shared_ptr<Z> x, std::shared_ptr<Z> y);
  __attribute__((pure)) static bool eqb(const std::shared_ptr<Z> &x,
                                        const std::shared_ptr<Z> &y);
};

struct ListDef {
  template <typename T1>
  static T1 nth(const unsigned int n, const std::shared_ptr<List<T1>> &l,
                const T1 default0);
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
  };

  __attribute__((pure)) static bool
  may_issue_batchall(const std::shared_ptr<Commander> &c);
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
  };

  __attribute__((pure)) static unsigned int
  unit_skill(const std::shared_ptr<Unit> &u);
  __attribute__((pure)) static unsigned int
  skill_bv_multiplier_num(const unsigned int skill);
  __attribute__((pure)) static unsigned int
  unit_base_bv(const std::shared_ptr<Unit> &u);
  __attribute__((pure)) static unsigned int
  unit_tech_bv(const std::shared_ptr<Unit> &u);
  __attribute__((pure)) static unsigned int
  unit_battle_value(const std::shared_ptr<Unit> &u);
  __attribute__((pure)) static unsigned int
  unit_effective_combat_rating(const std::shared_ptr<Unit> &u);
  using Force = std::shared_ptr<List<std::shared_ptr<Unit>>>;

  struct ForceMetrics {
    unsigned int fm_count;
    unsigned int fm_tonnage;
    unsigned int fm_elite_count;
    unsigned int fm_clan_count;
    unsigned int fm_total_bv;
    unsigned int fm_total_ecr;
  };

  static inline const std::shared_ptr<ForceMetrics> empty_metrics =
      std::make_shared<ForceMetrics>(ForceMetrics{0u, 0u, 0u, 0u, 0u, 0u});
  static std::shared_ptr<ForceMetrics>
  unit_to_metrics(const std::shared_ptr<Unit> &u);
  static std::shared_ptr<ForceMetrics>
  metrics_add(const std::shared_ptr<ForceMetrics> &m1,
              const std::shared_ptr<ForceMetrics> &m2);
  static std::shared_ptr<ForceMetrics>
  force_metrics(const std::shared_ptr<List<std::shared_ptr<Unit>>> &f);
  __attribute__((pure)) static bool
  metrics_total_lt(const std::shared_ptr<ForceMetrics> &m1,
                   const std::shared_ptr<ForceMetrics> &m2);
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
    std::shared_ptr<Commander> cm_commander;
    Force cm_force;
  };

  using Coalition = std::shared_ptr<List<std::shared_ptr<CoalitionMember>>>;
  __attribute__((pure)) static Force coalition_force(
      const std::shared_ptr<List<std::shared_ptr<CoalitionMember>>> &c);
  static std::shared_ptr<ForceMetrics> coalition_metrics(
      const std::shared_ptr<List<std::shared_ptr<CoalitionMember>>> &c);
  __attribute__((pure)) static bool coalition_contains_clan(
      const std::shared_ptr<List<std::shared_ptr<CoalitionMember>>> &c,
      const Clan clan);
  __attribute__((pure)) static unsigned int coalition_tonnage(
      const std::shared_ptr<List<std::shared_ptr<CoalitionMember>>> &c);

  struct CoalitionMemberBid {
    unsigned int cmb_member_index;
    Force cmb_new_force;
    Side cmb_side;
  };

  __attribute__((pure)) static Coalition update_coalition_force(
      const std::shared_ptr<List<std::shared_ptr<CoalitionMember>>> &c,
      const unsigned int idx,
      std::shared_ptr<List<std::shared_ptr<Unit>>> new_force);

  struct ForceBid {
    Force bid_force;
    Side bid_side;
    std::shared_ptr<Commander> bid_commander;
  };

  static std::shared_ptr<ForceMetrics>
  bid_metrics(const std::shared_ptr<ForceBid> &b);
  __attribute__((pure)) static std::optional<std::shared_ptr<Commander>>
  coalition_lead_commander(
      const std::shared_ptr<List<std::shared_ptr<CoalitionMember>>> &c);
  __attribute__((pure)) static std::optional<std::shared_ptr<ForceBid>>
  coalition_to_bid(
      const std::shared_ptr<List<std::shared_ptr<CoalitionMember>>> &c,
      const Side side);
  __attribute__((pure)) static Coalition apply_coalition_member_bid(
      const std::shared_ptr<List<std::shared_ptr<CoalitionMember>>> &c,
      const std::shared_ptr<CoalitionMemberBid> &cbid);
  __attribute__((pure)) static bool valid_coalition_member_bid_b(
      const std::shared_ptr<List<std::shared_ptr<CoalitionMember>>> &c,
      const std::shared_ptr<CoalitionMemberBid> &cbid);
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
    explicit Prize(PrizeHonor _v) : d_v_(_v) {}

    explicit Prize(PrizeEnclave _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<Prize> prizehonor() {
      return std::make_shared<Prize>(PrizeHonor{});
    }

    static std::shared_ptr<Prize> prizeenclave(unsigned int enclave_id) {
      return std::make_shared<Prize>(PrizeEnclave{std::move(enclave_id)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    template <typename T1, MapsTo<T1, unsigned int> F1>
    T1 Prize_rec(const T1 f, F1 &&f0) const {
      if (std::holds_alternative<typename Prize::PrizeHonor>(this->v())) {
        return f;
      } else {
        const auto &[d_enclave_id] =
            std::get<typename Prize::PrizeEnclave>(this->v());
        return f0(d_enclave_id);
      }
    }

    template <typename T1, MapsTo<T1, unsigned int> F1>
    T1 Prize_rect(const T1 f, F1 &&f0) const {
      if (std::holds_alternative<typename Prize::PrizeHonor>(this->v())) {
        return f;
      } else {
        const auto &[d_enclave_id] =
            std::get<typename Prize::PrizeEnclave>(this->v());
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
    explicit Location(LocPlanetSurface _v) : d_v_(std::move(_v)) {}

    explicit Location(LocEnclave _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<Location> locplanetsurface(unsigned int world_id,
                                                      unsigned int region_id) {
      return std::make_shared<Location>(
          LocPlanetSurface{std::move(world_id), std::move(region_id)});
    }

    static std::shared_ptr<Location> locenclave(unsigned int enclave_id) {
      return std::make_shared<Location>(LocEnclave{std::move(enclave_id)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    template <typename T1, MapsTo<T1, unsigned int, unsigned int> F0,
              MapsTo<T1, unsigned int> F1>
    T1 Location_rec(F0 &&f, F1 &&f0) const {
      if (std::holds_alternative<typename Location::LocPlanetSurface>(
              this->v())) {
        const auto &[d_world_id, d_region_id] =
            std::get<typename Location::LocPlanetSurface>(this->v());
        return f(d_world_id, d_region_id);
      } else {
        const auto &[d_enclave_id] =
            std::get<typename Location::LocEnclave>(this->v());
        return f0(d_enclave_id);
      }
    }

    template <typename T1, MapsTo<T1, unsigned int, unsigned int> F0,
              MapsTo<T1, unsigned int> F1>
    T1 Location_rect(F0 &&f, F1 &&f0) const {
      if (std::holds_alternative<typename Location::LocPlanetSurface>(
              this->v())) {
        const auto &[d_world_id, d_region_id] =
            std::get<typename Location::LocPlanetSurface>(this->v());
        return f(d_world_id, d_region_id);
      } else {
        const auto &[d_enclave_id] =
            std::get<typename Location::LocEnclave>(this->v());
        return f0(d_enclave_id);
      }
    }
  };

  struct BattleContext {
    bool ctx_hegira_allowed;
    bool ctx_circle_present;
  };

  static inline const std::shared_ptr<BattleContext>
      standard_possession_context =
          std::make_shared<BattleContext>(BattleContext{true, false});

  struct BatchallChallenge {
    std::shared_ptr<Commander> chal_challenger;
    Clan chal_clan;
    std::shared_ptr<Prize> chal_prize;
    Force chal_initial_force;
    std::shared_ptr<Location> chal_location;
    TrialType chal_trial_type;
    std::shared_ptr<BattleContext> chal_context;
  };

  struct BatchallResponse {
    std::shared_ptr<Commander> resp_defender;
    Clan resp_clan;
    Force resp_force;
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
    explicit RefusalReason(RefusalInsufficientRank _v) : d_v_(_v) {}

    explicit RefusalReason(RefusalOther _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<RefusalReason> refusalinsufficientrank() {
      return std::make_shared<RefusalReason>(RefusalInsufficientRank{});
    }

    static std::shared_ptr<RefusalReason> refusalother(unsigned int note) {
      return std::make_shared<RefusalReason>(RefusalOther{std::move(note)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    template <typename T1, MapsTo<T1, unsigned int> F1>
    T1 RefusalReason_rec(const T1 f, F1 &&f0) const {
      if (std::holds_alternative<
              typename RefusalReason::RefusalInsufficientRank>(this->v())) {
        return f;
      } else {
        const auto &[d_note] =
            std::get<typename RefusalReason::RefusalOther>(this->v());
        return f0(d_note);
      }
    }

    template <typename T1, MapsTo<T1, unsigned int> F1>
    T1 RefusalReason_rect(const T1 f, F1 &&f0) const {
      if (std::holds_alternative<
              typename RefusalReason::RefusalInsufficientRank>(this->v())) {
        return f;
      } else {
        const auto &[d_note] =
            std::get<typename RefusalReason::RefusalOther>(this->v());
        return f0(d_note);
      }
    }
  };

  struct ProtocolAction {
    // TYPES
    struct ActChallenge {
      std::shared_ptr<BatchallChallenge> d_chal;
    };

    struct ActRespond {
      std::shared_ptr<BatchallResponse> d_resp;
    };

    struct ActRefuse {
      std::shared_ptr<RefusalReason> d_reason;
    };

    struct ActBid {
      std::shared_ptr<ForceBid> d_bid;
    };

    struct ActCoalitionBid {
      std::shared_ptr<CoalitionMemberBid> d_cbid;
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
    explicit ProtocolAction(ActChallenge _v) : d_v_(std::move(_v)) {}

    explicit ProtocolAction(ActRespond _v) : d_v_(std::move(_v)) {}

    explicit ProtocolAction(ActRefuse _v) : d_v_(std::move(_v)) {}

    explicit ProtocolAction(ActBid _v) : d_v_(std::move(_v)) {}

    explicit ProtocolAction(ActCoalitionBid _v) : d_v_(std::move(_v)) {}

    explicit ProtocolAction(ActPass _v) : d_v_(std::move(_v)) {}

    explicit ProtocolAction(ActClose _v) : d_v_(_v) {}

    explicit ProtocolAction(ActWithdraw _v) : d_v_(std::move(_v)) {}

    explicit ProtocolAction(ActBreakBid _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<ProtocolAction>
    actchallenge(const std::shared_ptr<BatchallChallenge> &chal) {
      return std::make_shared<ProtocolAction>(ActChallenge{chal});
    }

    static std::shared_ptr<ProtocolAction>
    actchallenge(std::shared_ptr<BatchallChallenge> &&chal) {
      return std::make_shared<ProtocolAction>(ActChallenge{std::move(chal)});
    }

    static std::shared_ptr<ProtocolAction>
    actrespond(const std::shared_ptr<BatchallResponse> &resp) {
      return std::make_shared<ProtocolAction>(ActRespond{resp});
    }

    static std::shared_ptr<ProtocolAction>
    actrespond(std::shared_ptr<BatchallResponse> &&resp) {
      return std::make_shared<ProtocolAction>(ActRespond{std::move(resp)});
    }

    static std::shared_ptr<ProtocolAction>
    actrefuse(const std::shared_ptr<RefusalReason> &reason) {
      return std::make_shared<ProtocolAction>(ActRefuse{reason});
    }

    static std::shared_ptr<ProtocolAction>
    actrefuse(std::shared_ptr<RefusalReason> &&reason) {
      return std::make_shared<ProtocolAction>(ActRefuse{std::move(reason)});
    }

    static std::shared_ptr<ProtocolAction>
    actbid(const std::shared_ptr<ForceBid> &bid) {
      return std::make_shared<ProtocolAction>(ActBid{bid});
    }

    static std::shared_ptr<ProtocolAction>
    actbid(std::shared_ptr<ForceBid> &&bid) {
      return std::make_shared<ProtocolAction>(ActBid{std::move(bid)});
    }

    static std::shared_ptr<ProtocolAction>
    actcoalitionbid(const std::shared_ptr<CoalitionMemberBid> &cbid) {
      return std::make_shared<ProtocolAction>(ActCoalitionBid{cbid});
    }

    static std::shared_ptr<ProtocolAction>
    actcoalitionbid(std::shared_ptr<CoalitionMemberBid> &&cbid) {
      return std::make_shared<ProtocolAction>(ActCoalitionBid{std::move(cbid)});
    }

    static std::shared_ptr<ProtocolAction> actpass(Side side) {
      return std::make_shared<ProtocolAction>(ActPass{std::move(side)});
    }

    static std::shared_ptr<ProtocolAction> actclose() {
      return std::make_shared<ProtocolAction>(ActClose{});
    }

    static std::shared_ptr<ProtocolAction> actwithdraw(Side side) {
      return std::make_shared<ProtocolAction>(ActWithdraw{std::move(side)});
    }

    static std::shared_ptr<ProtocolAction> actbreakbid(Side side) {
      return std::make_shared<ProtocolAction>(ActBreakBid{std::move(side)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, std::shared_ptr<BatchallChallenge>> F0,
            MapsTo<T1, std::shared_ptr<BatchallResponse>> F1,
            MapsTo<T1, std::shared_ptr<RefusalReason>> F2,
            MapsTo<T1, std::shared_ptr<ForceBid>> F3,
            MapsTo<T1, std::shared_ptr<CoalitionMemberBid>> F4,
            MapsTo<T1, Side> F5, MapsTo<T1, Side> F7, MapsTo<T1, Side> F8>
  static T1 ProtocolAction_rect(F0 &&f, F1 &&f0, F2 &&f1, F3 &&f2, F4 &&f3,
                                F5 &&f4, const T1 f5, F7 &&f6, F8 &&f7,
                                const std::shared_ptr<ProtocolAction> &p) {
    if (std::holds_alternative<typename ProtocolAction::ActChallenge>(p->v())) {
      const auto &[d_chal] =
          std::get<typename ProtocolAction::ActChallenge>(p->v());
      return f(d_chal);
    } else if (std::holds_alternative<typename ProtocolAction::ActRespond>(
                   p->v())) {
      const auto &[d_resp] =
          std::get<typename ProtocolAction::ActRespond>(p->v());
      return f0(d_resp);
    } else if (std::holds_alternative<typename ProtocolAction::ActRefuse>(
                   p->v())) {
      const auto &[d_reason] =
          std::get<typename ProtocolAction::ActRefuse>(p->v());
      return f1(d_reason);
    } else if (std::holds_alternative<typename ProtocolAction::ActBid>(
                   p->v())) {
      const auto &[d_bid] = std::get<typename ProtocolAction::ActBid>(p->v());
      return f2(d_bid);
    } else if (std::holds_alternative<typename ProtocolAction::ActCoalitionBid>(
                   p->v())) {
      const auto &[d_cbid] =
          std::get<typename ProtocolAction::ActCoalitionBid>(p->v());
      return f3(d_cbid);
    } else if (std::holds_alternative<typename ProtocolAction::ActPass>(
                   p->v())) {
      const auto &[d_side] = std::get<typename ProtocolAction::ActPass>(p->v());
      return f4(d_side);
    } else if (std::holds_alternative<typename ProtocolAction::ActClose>(
                   p->v())) {
      return f5;
    } else if (std::holds_alternative<typename ProtocolAction::ActWithdraw>(
                   p->v())) {
      const auto &[d_side] =
          std::get<typename ProtocolAction::ActWithdraw>(p->v());
      return f6(d_side);
    } else {
      const auto &[d_side] =
          std::get<typename ProtocolAction::ActBreakBid>(p->v());
      return f7(d_side);
    }
  }

  template <typename T1, MapsTo<T1, std::shared_ptr<BatchallChallenge>> F0,
            MapsTo<T1, std::shared_ptr<BatchallResponse>> F1,
            MapsTo<T1, std::shared_ptr<RefusalReason>> F2,
            MapsTo<T1, std::shared_ptr<ForceBid>> F3,
            MapsTo<T1, std::shared_ptr<CoalitionMemberBid>> F4,
            MapsTo<T1, Side> F5, MapsTo<T1, Side> F7, MapsTo<T1, Side> F8>
  static T1 ProtocolAction_rec(F0 &&f, F1 &&f0, F2 &&f1, F3 &&f2, F4 &&f3,
                               F5 &&f4, const T1 f5, F7 &&f6, F8 &&f7,
                               const std::shared_ptr<ProtocolAction> &p) {
    if (std::holds_alternative<typename ProtocolAction::ActChallenge>(p->v())) {
      const auto &[d_chal] =
          std::get<typename ProtocolAction::ActChallenge>(p->v());
      return f(d_chal);
    } else if (std::holds_alternative<typename ProtocolAction::ActRespond>(
                   p->v())) {
      const auto &[d_resp] =
          std::get<typename ProtocolAction::ActRespond>(p->v());
      return f0(d_resp);
    } else if (std::holds_alternative<typename ProtocolAction::ActRefuse>(
                   p->v())) {
      const auto &[d_reason] =
          std::get<typename ProtocolAction::ActRefuse>(p->v());
      return f1(d_reason);
    } else if (std::holds_alternative<typename ProtocolAction::ActBid>(
                   p->v())) {
      const auto &[d_bid] = std::get<typename ProtocolAction::ActBid>(p->v());
      return f2(d_bid);
    } else if (std::holds_alternative<typename ProtocolAction::ActCoalitionBid>(
                   p->v())) {
      const auto &[d_cbid] =
          std::get<typename ProtocolAction::ActCoalitionBid>(p->v());
      return f3(d_cbid);
    } else if (std::holds_alternative<typename ProtocolAction::ActPass>(
                   p->v())) {
      const auto &[d_side] = std::get<typename ProtocolAction::ActPass>(p->v());
      return f4(d_side);
    } else if (std::holds_alternative<typename ProtocolAction::ActClose>(
                   p->v())) {
      return f5;
    } else if (std::holds_alternative<typename ProtocolAction::ActWithdraw>(
                   p->v())) {
      const auto &[d_side] =
          std::get<typename ProtocolAction::ActWithdraw>(p->v());
      return f6(d_side);
    } else {
      const auto &[d_side] =
          std::get<typename ProtocolAction::ActBreakBid>(p->v());
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
  __attribute__((pure)) static Force coalition_state_force(
      const std::optional<
          std::shared_ptr<List<std::shared_ptr<CoalitionMember>>>>
          cs,
      std::shared_ptr<List<std::shared_ptr<Unit>>> fallback);

  struct BatchallPhase : public std::enable_shared_from_this<BatchallPhase> {
    // TYPES
    struct PhaseIdle {};

    struct PhaseChallenged {
      std::shared_ptr<BatchallChallenge> d_challenge;
    };

    struct PhaseResponded {
      std::shared_ptr<BatchallChallenge> d_challenge;
      std::shared_ptr<BatchallResponse> d_response;
    };

    struct PhaseBidding {
      std::shared_ptr<BatchallChallenge> d_challenge;
      std::shared_ptr<BatchallResponse> d_response;
      std::shared_ptr<ForceBid> d_attacker_bid;
      std::shared_ptr<ForceBid> d_defender_bid;
      CoalitionState d_attacker_coalition;
      CoalitionState d_defender_coalition;
      std::shared_ptr<List<std::shared_ptr<ForceBid>>> d_bid_history;
      ReadyStatus d_ready;
    };

    struct PhaseAgreed {
      std::shared_ptr<BatchallChallenge> d_challenge;
      std::shared_ptr<BatchallResponse> d_response;
      std::shared_ptr<ForceBid> d_final_attacker;
      std::shared_ptr<ForceBid> d_final_defender;
    };

    struct PhaseRefused {
      std::shared_ptr<BatchallChallenge> d_challenge;
      std::shared_ptr<RefusalReason> d_reason;
    };

    struct PhaseAborted {
      std::shared_ptr<ProtocolAction> d_reason;
    };

    using variant_t =
        std::variant<PhaseIdle, PhaseChallenged, PhaseResponded, PhaseBidding,
                     PhaseAgreed, PhaseRefused, PhaseAborted>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    explicit BatchallPhase(PhaseIdle _v) : d_v_(_v) {}

    explicit BatchallPhase(PhaseChallenged _v) : d_v_(std::move(_v)) {}

    explicit BatchallPhase(PhaseResponded _v) : d_v_(std::move(_v)) {}

    explicit BatchallPhase(PhaseBidding _v) : d_v_(std::move(_v)) {}

    explicit BatchallPhase(PhaseAgreed _v) : d_v_(std::move(_v)) {}

    explicit BatchallPhase(PhaseRefused _v) : d_v_(std::move(_v)) {}

    explicit BatchallPhase(PhaseAborted _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<BatchallPhase> phaseidle() {
      return std::make_shared<BatchallPhase>(PhaseIdle{});
    }

    static std::shared_ptr<BatchallPhase>
    phasechallenged(const std::shared_ptr<BatchallChallenge> &challenge) {
      return std::make_shared<BatchallPhase>(PhaseChallenged{challenge});
    }

    static std::shared_ptr<BatchallPhase>
    phasechallenged(std::shared_ptr<BatchallChallenge> &&challenge) {
      return std::make_shared<BatchallPhase>(
          PhaseChallenged{std::move(challenge)});
    }

    static std::shared_ptr<BatchallPhase>
    phaseresponded(const std::shared_ptr<BatchallChallenge> &challenge,
                   const std::shared_ptr<BatchallResponse> &response) {
      return std::make_shared<BatchallPhase>(
          PhaseResponded{challenge, response});
    }

    static std::shared_ptr<BatchallPhase>
    phaseresponded(std::shared_ptr<BatchallChallenge> &&challenge,
                   std::shared_ptr<BatchallResponse> &&response) {
      return std::make_shared<BatchallPhase>(
          PhaseResponded{std::move(challenge), std::move(response)});
    }

    static std::shared_ptr<BatchallPhase> phasebidding(
        const std::shared_ptr<BatchallChallenge> &challenge,
        const std::shared_ptr<BatchallResponse> &response,
        const std::shared_ptr<ForceBid> &attacker_bid,
        const std::shared_ptr<ForceBid> &defender_bid,
        CoalitionState attacker_coalition, CoalitionState defender_coalition,
        const std::shared_ptr<List<std::shared_ptr<ForceBid>>> &bid_history,
        ReadyStatus ready) {
      return std::make_shared<BatchallPhase>(PhaseBidding{
          challenge, response, attacker_bid, defender_bid,
          std::move(attacker_coalition), std::move(defender_coalition),
          bid_history, std::move(ready)});
    }

    static std::shared_ptr<BatchallPhase>
    phasebidding(std::shared_ptr<BatchallChallenge> &&challenge,
                 std::shared_ptr<BatchallResponse> &&response,
                 std::shared_ptr<ForceBid> &&attacker_bid,
                 std::shared_ptr<ForceBid> &&defender_bid,
                 CoalitionState attacker_coalition,
                 CoalitionState defender_coalition,
                 std::shared_ptr<List<std::shared_ptr<ForceBid>>> &&bid_history,
                 ReadyStatus ready) {
      return std::make_shared<BatchallPhase>(PhaseBidding{
          std::move(challenge), std::move(response), std::move(attacker_bid),
          std::move(defender_bid), std::move(attacker_coalition),
          std::move(defender_coalition), std::move(bid_history),
          std::move(ready)});
    }

    static std::shared_ptr<BatchallPhase>
    phaseagreed(const std::shared_ptr<BatchallChallenge> &challenge,
                const std::shared_ptr<BatchallResponse> &response,
                const std::shared_ptr<ForceBid> &final_attacker,
                const std::shared_ptr<ForceBid> &final_defender) {
      return std::make_shared<BatchallPhase>(
          PhaseAgreed{challenge, response, final_attacker, final_defender});
    }

    static std::shared_ptr<BatchallPhase>
    phaseagreed(std::shared_ptr<BatchallChallenge> &&challenge,
                std::shared_ptr<BatchallResponse> &&response,
                std::shared_ptr<ForceBid> &&final_attacker,
                std::shared_ptr<ForceBid> &&final_defender) {
      return std::make_shared<BatchallPhase>(
          PhaseAgreed{std::move(challenge), std::move(response),
                      std::move(final_attacker), std::move(final_defender)});
    }

    static std::shared_ptr<BatchallPhase>
    phaserefused(const std::shared_ptr<BatchallChallenge> &challenge,
                 const std::shared_ptr<RefusalReason> &reason) {
      return std::make_shared<BatchallPhase>(PhaseRefused{challenge, reason});
    }

    static std::shared_ptr<BatchallPhase>
    phaserefused(std::shared_ptr<BatchallChallenge> &&challenge,
                 std::shared_ptr<RefusalReason> &&reason) {
      return std::make_shared<BatchallPhase>(
          PhaseRefused{std::move(challenge), std::move(reason)});
    }

    static std::shared_ptr<BatchallPhase>
    phaseaborted(const std::shared_ptr<ProtocolAction> &reason) {
      return std::make_shared<BatchallPhase>(PhaseAborted{reason});
    }

    static std::shared_ptr<BatchallPhase>
    phaseaborted(std::shared_ptr<ProtocolAction> &&reason) {
      return std::make_shared<BatchallPhase>(PhaseAborted{std::move(reason)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    __attribute__((pure)) std::optional<std::shared_ptr<Commander>>
    action_actor_in_phase(const std::shared_ptr<ProtocolAction> &action) const {
      if (std::holds_alternative<typename ProtocolAction::ActChallenge>(
              action->v())) {
        const auto &[d_chal] =
            std::get<typename ProtocolAction::ActChallenge>(action->v());
        return std::make_optional<std::shared_ptr<Commander>>(
            d_chal->chal_challenger);
      } else if (std::holds_alternative<typename ProtocolAction::ActRespond>(
                     action->v())) {
        const auto &[d_resp] =
            std::get<typename ProtocolAction::ActRespond>(action->v());
        return std::make_optional<std::shared_ptr<Commander>>(
            d_resp->resp_defender);
      } else if (std::holds_alternative<typename ProtocolAction::ActBid>(
                     action->v())) {
        const auto &[d_bid] =
            std::get<typename ProtocolAction::ActBid>(action->v());
        return std::make_optional<std::shared_ptr<Commander>>(
            d_bid->bid_commander);
      } else if (std::holds_alternative<typename ProtocolAction::ActWithdraw>(
                     action->v())) {
        const auto &[d_side] =
            std::get<typename ProtocolAction::ActWithdraw>(action->v());
        return std::const_pointer_cast<BatchallPhase>(this->shared_from_this())
            ->get_side_commander(d_side);
      } else if (std::holds_alternative<typename ProtocolAction::ActBreakBid>(
                     action->v())) {
        const auto &[d_side] =
            std::get<typename ProtocolAction::ActBreakBid>(action->v());
        return std::const_pointer_cast<BatchallPhase>(this->shared_from_this())
            ->get_side_commander(d_side);
      } else {
        return std::optional<std::shared_ptr<Commander>>();
      }
    }

    __attribute__((pure)) std::optional<std::shared_ptr<Commander>>
    get_side_commander(const Side side) const {
      if (std::holds_alternative<typename BatchallPhase::PhaseBidding>(
              this->v())) {
        const auto &[d_challenge, d_response, d_attacker_bid, d_defender_bid,
                     d_attacker_coalition, d_defender_coalition, d_bid_history,
                     d_ready] =
            std::get<typename BatchallPhase::PhaseBidding>(this->v());
        switch (side) {
        case Side::e_ATTACKER: {
          return std::make_optional<std::shared_ptr<Commander>>(
              d_attacker_bid->bid_commander);
        }
        case Side::e_DEFENDER: {
          return std::make_optional<std::shared_ptr<Commander>>(
              d_defender_bid->bid_commander);
        }
        default:
          std::unreachable();
        }
      } else {
        return std::optional<std::shared_ptr<Commander>>();
      }
    }

    __attribute__((pure)) unsigned int get_bidding_measure() const {
      if (std::holds_alternative<typename BatchallPhase::PhaseBidding>(
              this->v())) {
        const auto &[d_challenge, d_response, d_attacker_bid, d_defender_bid,
                     d_attacker_coalition, d_defender_coalition, d_bid_history,
                     d_ready] =
            std::get<typename BatchallPhase::PhaseBidding>(this->v());
        return ((bid_metrics(d_attacker_bid)->fm_total_ecr +
                 bid_metrics(d_defender_bid)->fm_total_ecr) +
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
      if (std::holds_alternative<typename BatchallPhase::PhaseIdle>(
              this->v())) {
        return 4u;
      } else if (std::holds_alternative<
                     typename BatchallPhase::PhaseChallenged>(this->v())) {
        return 3u;
      } else if (std::holds_alternative<typename BatchallPhase::PhaseResponded>(
                     this->v())) {
        return 2u;
      } else if (std::holds_alternative<typename BatchallPhase::PhaseBidding>(
                     this->v())) {
        return 1u;
      } else {
        return 0u;
      }
    }

    __attribute__((pure)) bool is_bidding() const {
      if (std::holds_alternative<typename BatchallPhase::PhaseBidding>(
              this->v())) {
        return true;
      } else {
        return false;
      }
    }

    __attribute__((pure)) bool is_terminal() const {
      if (std::holds_alternative<typename BatchallPhase::PhaseAgreed>(
              this->v())) {
        return true;
      } else if (std::holds_alternative<typename BatchallPhase::PhaseRefused>(
                     this->v())) {
        return true;
      } else if (std::holds_alternative<typename BatchallPhase::PhaseAborted>(
                     this->v())) {
        return true;
      } else {
        return false;
      }
    }
  };

  template <
      typename T1, MapsTo<T1, std::shared_ptr<BatchallChallenge>> F1,
      MapsTo<T1, std::shared_ptr<BatchallChallenge>,
             std::shared_ptr<BatchallResponse>>
          F2,
      MapsTo<T1, std::shared_ptr<BatchallChallenge>,
             std::shared_ptr<BatchallResponse>, std::shared_ptr<ForceBid>,
             std::shared_ptr<ForceBid>,
             std::optional<
                 std::shared_ptr<List<std::shared_ptr<CoalitionMember>>>>,
             std::optional<
                 std::shared_ptr<List<std::shared_ptr<CoalitionMember>>>>,
             std::shared_ptr<List<std::shared_ptr<ForceBid>>>, ReadyStatus>
          F3,
      MapsTo<T1, std::shared_ptr<BatchallChallenge>,
             std::shared_ptr<BatchallResponse>, std::shared_ptr<ForceBid>,
             std::shared_ptr<ForceBid>>
          F4,
      MapsTo<T1, std::shared_ptr<BatchallChallenge>,
             std::shared_ptr<RefusalReason>>
          F5,
      MapsTo<T1, std::shared_ptr<ProtocolAction>> F6>
  static T1 BatchallPhase_rect(const T1 f, F1 &&f0, F2 &&f1, F3 &&f2, F4 &&f3,
                               F5 &&f4, F6 &&f5,
                               const std::shared_ptr<BatchallPhase> &b) {
    if (std::holds_alternative<typename BatchallPhase::PhaseIdle>(b->v())) {
      return f;
    } else if (std::holds_alternative<typename BatchallPhase::PhaseChallenged>(
                   b->v())) {
      const auto &[d_challenge] =
          std::get<typename BatchallPhase::PhaseChallenged>(b->v());
      return f0(d_challenge);
    } else if (std::holds_alternative<typename BatchallPhase::PhaseResponded>(
                   b->v())) {
      const auto &[d_challenge, d_response] =
          std::get<typename BatchallPhase::PhaseResponded>(b->v());
      return f1(d_challenge, d_response);
    } else if (std::holds_alternative<typename BatchallPhase::PhaseBidding>(
                   b->v())) {
      const auto &[d_challenge, d_response, d_attacker_bid, d_defender_bid,
                   d_attacker_coalition, d_defender_coalition, d_bid_history,
                   d_ready] =
          std::get<typename BatchallPhase::PhaseBidding>(b->v());
      return f2(d_challenge, d_response, d_attacker_bid, d_defender_bid,
                d_attacker_coalition, d_defender_coalition, d_bid_history,
                d_ready);
    } else if (std::holds_alternative<typename BatchallPhase::PhaseAgreed>(
                   b->v())) {
      const auto &[d_challenge, d_response, d_final_attacker,
                   d_final_defender] =
          std::get<typename BatchallPhase::PhaseAgreed>(b->v());
      return f3(d_challenge, d_response, d_final_attacker, d_final_defender);
    } else if (std::holds_alternative<typename BatchallPhase::PhaseRefused>(
                   b->v())) {
      const auto &[d_challenge, d_reason] =
          std::get<typename BatchallPhase::PhaseRefused>(b->v());
      return f4(d_challenge, d_reason);
    } else {
      const auto &[d_reason] =
          std::get<typename BatchallPhase::PhaseAborted>(b->v());
      return f5(d_reason);
    }
  }

  template <
      typename T1, MapsTo<T1, std::shared_ptr<BatchallChallenge>> F1,
      MapsTo<T1, std::shared_ptr<BatchallChallenge>,
             std::shared_ptr<BatchallResponse>>
          F2,
      MapsTo<T1, std::shared_ptr<BatchallChallenge>,
             std::shared_ptr<BatchallResponse>, std::shared_ptr<ForceBid>,
             std::shared_ptr<ForceBid>,
             std::optional<
                 std::shared_ptr<List<std::shared_ptr<CoalitionMember>>>>,
             std::optional<
                 std::shared_ptr<List<std::shared_ptr<CoalitionMember>>>>,
             std::shared_ptr<List<std::shared_ptr<ForceBid>>>, ReadyStatus>
          F3,
      MapsTo<T1, std::shared_ptr<BatchallChallenge>,
             std::shared_ptr<BatchallResponse>, std::shared_ptr<ForceBid>,
             std::shared_ptr<ForceBid>>
          F4,
      MapsTo<T1, std::shared_ptr<BatchallChallenge>,
             std::shared_ptr<RefusalReason>>
          F5,
      MapsTo<T1, std::shared_ptr<ProtocolAction>> F6>
  static T1 BatchallPhase_rec(const T1 f, F1 &&f0, F2 &&f1, F3 &&f2, F4 &&f3,
                              F5 &&f4, F6 &&f5,
                              const std::shared_ptr<BatchallPhase> &b) {
    if (std::holds_alternative<typename BatchallPhase::PhaseIdle>(b->v())) {
      return f;
    } else if (std::holds_alternative<typename BatchallPhase::PhaseChallenged>(
                   b->v())) {
      const auto &[d_challenge] =
          std::get<typename BatchallPhase::PhaseChallenged>(b->v());
      return f0(d_challenge);
    } else if (std::holds_alternative<typename BatchallPhase::PhaseResponded>(
                   b->v())) {
      const auto &[d_challenge, d_response] =
          std::get<typename BatchallPhase::PhaseResponded>(b->v());
      return f1(d_challenge, d_response);
    } else if (std::holds_alternative<typename BatchallPhase::PhaseBidding>(
                   b->v())) {
      const auto &[d_challenge, d_response, d_attacker_bid, d_defender_bid,
                   d_attacker_coalition, d_defender_coalition, d_bid_history,
                   d_ready] =
          std::get<typename BatchallPhase::PhaseBidding>(b->v());
      return f2(d_challenge, d_response, d_attacker_bid, d_defender_bid,
                d_attacker_coalition, d_defender_coalition, d_bid_history,
                d_ready);
    } else if (std::holds_alternative<typename BatchallPhase::PhaseAgreed>(
                   b->v())) {
      const auto &[d_challenge, d_response, d_final_attacker,
                   d_final_defender] =
          std::get<typename BatchallPhase::PhaseAgreed>(b->v());
      return f3(d_challenge, d_response, d_final_attacker, d_final_defender);
    } else if (std::holds_alternative<typename BatchallPhase::PhaseRefused>(
                   b->v())) {
      const auto &[d_challenge, d_reason] =
          std::get<typename BatchallPhase::PhaseRefused>(b->v());
      return f4(d_challenge, d_reason);
    } else {
      const auto &[d_reason] =
          std::get<typename BatchallPhase::PhaseAborted>(b->v());
      return f5(d_reason);
    }
  }

  using Honor = std::shared_ptr<Z>;
  using HonorEntry = std::pair<unsigned int, Honor>;
  using HonorLedger = std::shared_ptr<List<HonorEntry>>;
  __attribute__((pure)) static Honor ledger_lookup(
      const std::shared_ptr<List<std::pair<unsigned int, std::shared_ptr<Z>>>>
          &ledger,
      const unsigned int warrior_id);
  __attribute__((pure)) static HonorLedger ledger_update_by_id(
      const std::shared_ptr<List<std::pair<unsigned int, std::shared_ptr<Z>>>>
          &ledger,
      const unsigned int warrior_id, std::shared_ptr<Z> new_honor);
  __attribute__((pure)) static HonorLedger update_honor(
      const std::shared_ptr<List<std::pair<unsigned int, std::shared_ptr<Z>>>>
          &ledger,
      const std::shared_ptr<Commander> &actor, const std::shared_ptr<Z> &delta);
  __attribute__((pure)) static Honor
  refusal_honor_delta(const std::shared_ptr<RefusalReason> &r);
  __attribute__((pure)) static Honor
  protocol_honor_delta(const std::shared_ptr<ProtocolAction> &action);

  struct BatchallState {
    std::shared_ptr<BatchallPhase> bs_phase;
    HonorLedger bs_honor;
  };

  static inline const HonorLedger empty_ledger =
      List<std::pair<unsigned int, std::shared_ptr<Z>>>::nil();
  static inline const std::shared_ptr<BatchallState> initial_state =
      std::make_shared<BatchallState>(
          BatchallState{BatchallPhase::phaseidle(), empty_ledger});
  __attribute__((pure)) static HonorLedger
  apply_action_honor(const std::shared_ptr<BatchallState> &state,
                     const std::shared_ptr<ProtocolAction> &action);
  static inline const std::shared_ptr<Commander> malthus =
      std::make_shared<Commander>(
          Commander{1u, Clan::e_CLANJADEFALCON, Rank::e_STARCOLONEL, true});
  static inline const std::shared_ptr<Commander> radick =
      std::make_shared<Commander>(
          Commander{2u, Clan::e_CLANWOLF, Rank::e_STARCAPTAIN, true});
  static inline const std::shared_ptr<Commander> bear_ally =
      std::make_shared<Commander>(
          Commander{3u, Clan::e_CLANGHOSTBEAR, Rank::e_STARCAPTAIN, false});
  static inline const std::shared_ptr<Unit> timberwolf = std::make_shared<Unit>(
      Unit{101u, UnitClass::e_OMNIMECH, WeightClass::e_HEAVY, 75u, 2u, 3u, true,
           true});
  static inline const std::shared_ptr<Unit> direwolf = std::make_shared<Unit>(
      Unit{102u, UnitClass::e_OMNIMECH, WeightClass::e_ASSAULT, 100u, 2u, 3u,
           true, true});
  static inline const std::shared_ptr<Unit> summoner = std::make_shared<Unit>(
      Unit{103u, UnitClass::e_OMNIMECH, WeightClass::e_HEAVY, 70u, 3u, 4u,
           false, true});
  static inline const std::shared_ptr<Unit> mad_dog = std::make_shared<Unit>(
      Unit{104u, UnitClass::e_OMNIMECH, WeightClass::e_HEAVY, 60u, 3u, 4u,
           false, true});
  static inline const std::shared_ptr<Unit> elementals = std::make_shared<Unit>(
      Unit{105u, UnitClass::e_ELEMENTAL, WeightClass::e_LIGHT, 5u, 3u, 4u,
           false, true});
  static inline const Force falcon_trinary = List<std::shared_ptr<Unit>>::cons(
      direwolf,
      List<std::shared_ptr<Unit>>::cons(
          timberwolf,
          List<std::shared_ptr<Unit>>::cons(
              summoner, List<std::shared_ptr<Unit>>::cons(
                            mad_dog, List<std::shared_ptr<Unit>>::nil()))));
  static inline const Force wolf_binary = List<std::shared_ptr<Unit>>::cons(
      timberwolf, List<std::shared_ptr<Unit>>::cons(
                      summoner, List<std::shared_ptr<Unit>>::nil()));
  static inline const Force bear_support = List<std::shared_ptr<Unit>>::cons(
      elementals, List<std::shared_ptr<Unit>>::cons(
                      elementals, List<std::shared_ptr<Unit>>::nil()));
  static inline const Coalition attacker_coalition =
      List<std::shared_ptr<CoalitionMember>>::cons(
          std::make_shared<CoalitionMember>(
              CoalitionMember{Clan::e_CLANJADEFALCON, malthus, falcon_trinary}),
          List<std::shared_ptr<CoalitionMember>>::cons(
              std::make_shared<CoalitionMember>(CoalitionMember{
                  Clan::e_CLANGHOSTBEAR, bear_ally, bear_support}),
              List<std::shared_ptr<CoalitionMember>>::nil()));
  static inline const Coalition defender_coalition =
      List<std::shared_ptr<CoalitionMember>>::cons(
          std::make_shared<CoalitionMember>(
              CoalitionMember{Clan::e_CLANWOLF, radick, wolf_binary}),
          List<std::shared_ptr<CoalitionMember>>::nil());
  static inline const std::shared_ptr<BatchallChallenge> sample_challenge =
      std::make_shared<BatchallChallenge>(BatchallChallenge{
          malthus, Clan::e_CLANJADEFALCON, Prize::prizeenclave(42u),
          coalition_force(attacker_coalition),
          Location::locplanetsurface(7u, 3u), TrialType::e_TRIALOFPOSSESSION,
          standard_possession_context});
  static inline const std::shared_ptr<BatchallResponse> sample_response =
      std::make_shared<BatchallResponse>(BatchallResponse{
          radick, Clan::e_CLANWOLF, coalition_force(defender_coalition)});
  static inline const std::shared_ptr<ForceBid> sample_attacker_bid =
      []() -> std::shared_ptr<ForceBid> {
    auto _cs = coalition_to_bid(attacker_coalition, Side::e_ATTACKER);
    if (_cs.has_value()) {
      const std::shared_ptr<ForceBid> &bid = *_cs;
      return bid;
    } else {
      return std::make_shared<ForceBid>(ForceBid{
          List<std::shared_ptr<Unit>>::nil(), Side::e_ATTACKER, malthus});
    }
  }();
  static inline const std::shared_ptr<ForceBid> sample_defender_bid =
      []() -> std::shared_ptr<ForceBid> {
    auto _cs = coalition_to_bid(defender_coalition, Side::e_DEFENDER);
    if (_cs.has_value()) {
      const std::shared_ptr<ForceBid> &bid = *_cs;
      return bid;
    } else {
      return std::make_shared<ForceBid>(ForceBid{
          List<std::shared_ptr<Unit>>::nil(), Side::e_DEFENDER, radick});
    }
  }();
  static inline const Force reduced_support_force =
      List<std::shared_ptr<Unit>>::cons(elementals,
                                        List<std::shared_ptr<Unit>>::nil());
  static inline const std::shared_ptr<CoalitionMemberBid>
      sample_coalition_member_bid = std::make_shared<CoalitionMemberBid>(
          CoalitionMemberBid{1u, reduced_support_force, Side::e_ATTACKER});
  static inline const Coalition updated_attacker_coalition =
      apply_coalition_member_bid(attacker_coalition,
                                 sample_coalition_member_bid);
  static inline const std::shared_ptr<ForceBid> updated_attacker_bid =
      []() -> std::shared_ptr<ForceBid> {
    auto _cs = coalition_to_bid(updated_attacker_coalition, Side::e_ATTACKER);
    if (_cs.has_value()) {
      const std::shared_ptr<ForceBid> &bid = *_cs;
      return bid;
    } else {
      return sample_attacker_bid;
    }
  }();
  static inline const std::shared_ptr<BatchallPhase> phase_after_initial_bid =
      BatchallPhase::phasebidding(
          sample_challenge, sample_response, sample_attacker_bid,
          sample_defender_bid,
          std::make_optional<
              std::shared_ptr<List<std::shared_ptr<CoalitionMember>>>>(
              attacker_coalition),
          std::make_optional<
              std::shared_ptr<List<std::shared_ptr<CoalitionMember>>>>(
              defender_coalition),
          List<std::shared_ptr<ForceBid>>::nil(), ReadyStatus::e_NEITHERREADY);
  static inline const std::shared_ptr<BatchallPhase> phase_after_attacker_pass =
      BatchallPhase::phasebidding(
          sample_challenge, sample_response, sample_attacker_bid,
          sample_defender_bid,
          std::make_optional<
              std::shared_ptr<List<std::shared_ptr<CoalitionMember>>>>(
              attacker_coalition),
          std::make_optional<
              std::shared_ptr<List<std::shared_ptr<CoalitionMember>>>>(
              defender_coalition),
          List<std::shared_ptr<ForceBid>>::nil(), ReadyStatus::e_ATTACKERREADY);
  static inline const std::shared_ptr<BatchallPhase> phase_after_coalition_bid =
      BatchallPhase::phasebidding(
          sample_challenge, sample_response, updated_attacker_bid,
          sample_defender_bid,
          std::make_optional<
              std::shared_ptr<List<std::shared_ptr<CoalitionMember>>>>(
              updated_attacker_coalition),
          std::make_optional<
              std::shared_ptr<List<std::shared_ptr<CoalitionMember>>>>(
              defender_coalition),
          List<std::shared_ptr<ForceBid>>::cons(
              sample_attacker_bid, List<std::shared_ptr<ForceBid>>::nil()),
          ReadyStatus::e_NEITHERREADY);
  static inline const std::shared_ptr<BatchallPhase> phase_agreed =
      BatchallPhase::phaseagreed(sample_challenge, sample_response,
                                 updated_attacker_bid, sample_defender_bid);
  static inline const std::shared_ptr<BatchallState> state_after_initial_bid =
      std::make_shared<BatchallState>(
          BatchallState{phase_after_initial_bid, empty_ledger});
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
      phase_after_initial_bid->is_bidding();
  static inline const bool sample_agreed_terminal = phase_agreed->is_terminal();
  static inline const unsigned int sample_phase_depth_before_close =
      phase_after_initial_bid->phase_depth();
  static inline const unsigned int sample_phase_depth_after_close =
      phase_agreed->phase_depth();
  static inline const bool sample_bidding_measure_reduced =
      phase_after_coalition_bid->get_bidding_measure() <
      phase_after_initial_bid->get_bidding_measure();
  static inline const Honor sample_challenge_honor =
      ledger_lookup(sample_challenge_honor_ledger, malthus->cmd_id);
  static inline const Honor sample_break_bid_honor =
      ledger_lookup(sample_break_bid_honor_ledger, malthus->cmd_id);
  static inline const bool sample_challenge_honor_is_one =
      BinInt::eqb(sample_challenge_honor, Z::zpos(Positive::xh()));
  static inline const bool sample_break_bid_honor_is_minus_ten = BinInt::eqb(
      sample_break_bid_honor,
      Z::zneg(Positive::xo(Positive::xi(Positive::xo(Positive::xh())))));
  static inline const unsigned int sample_break_bid_actor_id =
      []() -> unsigned int {
    auto _cs = phase_after_initial_bid->action_actor_in_phase(
        ProtocolAction::actbreakbid(Side::e_ATTACKER));
    if (_cs.has_value()) {
      const std::shared_ptr<Commander> &cmd = *_cs;
      return cmd->cmd_id;
    } else {
      return 0u;
    }
  }();
  static inline const unsigned int sample_attacker_bid_count =
      bid_metrics(sample_attacker_bid)->fm_count;
  static inline const unsigned int sample_updated_bid_count =
      bid_metrics(updated_attacker_bid)->fm_count;
  static inline const unsigned int sample_state_force_count =
      coalition_state_force(
          std::make_optional<
              std::shared_ptr<List<std::shared_ptr<CoalitionMember>>>>(
              attacker_coalition),
          List<std::shared_ptr<Unit>>::nil())
          ->length();
};

template <typename T1>
T1 ListDef::nth(const unsigned int n, const std::shared_ptr<List<T1>> &l,
                const T1 default0) {
  if (n <= 0) {
    if (std::holds_alternative<typename List<T1>::Nil>(l->v())) {
      return default0;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<T1>::Cons>(l->v());
      return d_a0;
    }
  } else {
    unsigned int m = n - 1;
    if (std::holds_alternative<typename List<T1>::Nil>(l->v())) {
      return default0;
    } else {
      const auto &[d_a00, d_a10] = std::get<typename List<T1>::Cons>(l->v());
      return ListDef::template nth<T1>(m, d_a10, default0);
    }
  }
}

#endif // INCLUDED_COALITION_BID_HONOR_TRACE
