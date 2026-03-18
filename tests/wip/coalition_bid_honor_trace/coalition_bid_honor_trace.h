#ifndef INCLUDED_COALITION_BID_HONOR_TRACE
#define INCLUDED_COALITION_BID_HONOR_TRACE

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

  template <MapsTo<bool, t_A> F0>
  __attribute__((pure)) bool existsb(F0 &&f) const {
    return std::visit(
        Overloaded{
            [](const typename List<t_A>::Nil _args) -> bool { return false; },
            [&](const typename List<t_A>::Cons _args) -> bool {
              return (f(_args.d_a0) || _args.d_a1->existsb(f));
            }},
        this->v());
  }

  template <typename T1, MapsTo<T1, t_A, T1> F0>
  T1 fold_right(F0 &&f, const T1 a0) const {
    return std::visit(
        Overloaded{
            [&](const typename List<t_A>::Nil _args) -> T1 { return a0; },
            [&](const typename List<t_A>::Cons _args) -> T1 {
              return f(_args.d_a0, _args.d_a1->template fold_right<T1>(f, a0));
            }},
        this->v());
  }

  template <typename T1, MapsTo<std::shared_ptr<List<T1>>, t_A> F0>
  std::shared_ptr<List<T1>> flat_map(F0 &&f) const {
    return std::visit(
        Overloaded{
            [](const typename List<t_A>::Nil _args)
                -> std::shared_ptr<List<T1>> { return List<T1>::ctor::Nil_(); },
            [&](const typename List<t_A>::Cons _args)
                -> std::shared_ptr<List<T1>> {
              return f(_args.d_a0)->app(_args.d_a1->template flat_map<T1>(f));
            }},
        this->v());
  }

  t_A nth(const unsigned int n, const t_A default0) const {
    if (n <= 0) {
      return std::visit(
          Overloaded{[&](const typename List<t_A>::Nil _args) -> t_A {
                       return default0;
                     },
                     [](const typename List<t_A>::Cons _args) -> t_A {
                       return _args.d_a0;
                     }},
          this->v());
    } else {
      unsigned int m = n - 1;
      return std::visit(
          Overloaded{[&](const typename List<t_A>::Nil _args0) -> t_A {
                       return default0;
                     },
                     [&](const typename List<t_A>::Cons _args0) -> t_A {
                       return _args0.d_a1->nth(m, default0);
                     }},
          this->v());
    }
  }

  template <typename T1, MapsTo<T1, t_A> F0>
  std::shared_ptr<List<T1>> map(F0 &&f) const {
    return std::visit(
        Overloaded{
            [](const typename List<t_A>::Nil _args)
                -> std::shared_ptr<List<T1>> { return List<T1>::ctor::Nil_(); },
            [&](const typename List<t_A>::Cons _args)
                -> std::shared_ptr<List<T1>> {
              return List<T1>::ctor::Cons_(f(_args.d_a0),
                                           _args.d_a1->template map<T1>(f));
            }},
        this->v());
  }

  __attribute__((pure)) unsigned int length() const {
    return std::visit(
        Overloaded{[](const typename List<t_A>::Nil _args) -> unsigned int {
                     return 0u;
                   },
                   [](const typename List<t_A>::Cons _args) -> unsigned int {
                     return (_args.d_a1->length() + 1);
                   }},
        this->v());
  }

  std::shared_ptr<List<t_A>> app(std::shared_ptr<List<t_A>> m) const {
    return std::visit(
        Overloaded{[&](const typename List<t_A>::Nil _args)
                       -> std::shared_ptr<List<t_A>> { return m; },
                   [&](const typename List<t_A>::Cons _args)
                       -> std::shared_ptr<List<t_A>> {
                     return List<t_A>::ctor::Cons_(_args.d_a0,
                                                   _args.d_a1->app(m));
                   }},
        this->v());
  }
};

struct PeanoNat {
  __attribute__((pure)) static bool eqb(const unsigned int n,
                                        const unsigned int m);
  __attribute__((pure)) static bool leb(const unsigned int n,
                                        const unsigned int m);
  __attribute__((pure)) static bool ltb(const unsigned int n,
                                        const unsigned int m);
  __attribute__((pure)) static std::pair<unsigned int, unsigned int>
  divmod(const unsigned int x, const unsigned int y, const unsigned int q,
         const unsigned int u);
  __attribute__((pure)) static unsigned int div(const unsigned int x,
                                                const unsigned int y);
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

struct CoalitionBidHonorTraceCase {
  enum class Clan { e_CLANWOLF, e_CLANJADEFALCON, e_CLANGHOSTBEAR };

  template <typename T1>
  static T1 Clan_rect(const T1 f, const T1 f0, const T1 f1, const Clan c) {
    return [&](void) {
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
      }
    }();
  }

  template <typename T1>
  static T1 Clan_rec(const T1 f, const T1 f0, const T1 f1, const Clan c) {
    return [&](void) {
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
      }
    }();
  }

  __attribute__((pure)) static bool clan_eq_dec(const Clan c1, const Clan c2);
  __attribute__((pure)) static bool clan_eqb(const Clan c1, const Clan c2);
  enum class Rank { e_WARRIOR, e_STARCAPTAIN, e_STARCOLONEL };

  template <typename T1>
  static T1 Rank_rect(const T1 f, const T1 f0, const T1 f1, const Rank r) {
    return [&](void) {
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
      }
    }();
  }

  template <typename T1>
  static T1 Rank_rec(const T1 f, const T1 f0, const T1 f1, const Rank r) {
    return [&](void) {
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
      }
    }();
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
    return [&](void) {
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
      }
    }();
  }

  template <typename T1>
  static T1 UnitClass_rec(const T1 f, const T1 f0, const T1 f1,
                          const UnitClass u) {
    return [&](void) {
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
      }
    }();
  }
  enum class WeightClass { e_LIGHT, e_HEAVY, e_ASSAULT };

  template <typename T1>
  static T1 WeightClass_rect(const T1 f, const T1 f0, const T1 f1,
                             const WeightClass w) {
    return [&](void) {
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
      }
    }();
  }

  template <typename T1>
  static T1 WeightClass_rec(const T1 f, const T1 f0, const T1 f1,
                            const WeightClass w) {
    return [&](void) {
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
      }
    }();
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
  static std::shared_ptr<ForceMetrics> unit_to_metrics(std::shared_ptr<Unit> u);
  static std::shared_ptr<ForceMetrics>
  metrics_add(std::shared_ptr<ForceMetrics> m1,
              std::shared_ptr<ForceMetrics> m2);
  static std::shared_ptr<ForceMetrics>
  force_metrics(const std::shared_ptr<List<std::shared_ptr<Unit>>> &f);
  __attribute__((pure)) static bool
  metrics_total_lt(const std::shared_ptr<ForceMetrics> &m1,
                   const std::shared_ptr<ForceMetrics> &m2);
  enum class Side { e_ATTACKER, e_DEFENDER };

  template <typename T1>
  static T1 Side_rect(const T1 f, const T1 f0, const Side s) {
    return [&](void) {
      switch (s) {
      case Side::e_ATTACKER: {
        return f;
      }
      case Side::e_DEFENDER: {
        return f0;
      }
      }
    }();
  }

  template <typename T1>
  static T1 Side_rec(const T1 f, const T1 f0, const Side s) {
    return [&](void) {
      switch (s) {
      case Side::e_ATTACKER: {
        return f;
      }
      case Side::e_DEFENDER: {
        return f0;
      }
      }
    }();
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
  coalition_to_bid(std::shared_ptr<List<std::shared_ptr<CoalitionMember>>> c,
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
    return [&](void) {
      switch (t) {
      case TrialType::e_TRIALOFPOSSESSION: {
        return f;
      }
      case TrialType::e_TRIALOFANNIHILATION: {
        return f0;
      }
      }
    }();
  }

  template <typename T1>
  static T1 TrialType_rec(const T1 f, const T1 f0, const TrialType t) {
    return [&](void) {
      switch (t) {
      case TrialType::e_TRIALOFPOSSESSION: {
        return f;
      }
      case TrialType::e_TRIALOFANNIHILATION: {
        return f0;
      }
      }
    }();
  }

  struct Prize {
    // TYPES
    struct PrizeHonor {};

    struct PrizeEnclave {
      unsigned int d_a0;
    };

    using variant_t = std::variant<PrizeHonor, PrizeEnclave>;

  private:
    // DATA
    variant_t d_v_;

    // CREATORS
    explicit Prize(PrizeHonor _v) : d_v_(std::move(_v)) {}

    explicit Prize(PrizeEnclave _v) : d_v_(std::move(_v)) {}

  public:
    // TYPES
    struct ctor {
      ctor() = delete;

      static std::shared_ptr<Prize> PrizeHonor_() {
        return std::shared_ptr<Prize>(new Prize(PrizeHonor{}));
      }

      static std::shared_ptr<Prize> PrizeEnclave_(unsigned int a0) {
        return std::shared_ptr<Prize>(new Prize(PrizeEnclave{a0}));
      }

      static std::unique_ptr<Prize> PrizeHonor_uptr() {
        return std::unique_ptr<Prize>(new Prize(PrizeHonor{}));
      }

      static std::unique_ptr<Prize> PrizeEnclave_uptr(unsigned int a0) {
        return std::unique_ptr<Prize>(new Prize(PrizeEnclave{a0}));
      }
    };

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, unsigned int> F1>
  static T1 Prize_rect(const T1 f, F1 &&f0, const std::shared_ptr<Prize> &p) {
    return std::visit(
        Overloaded{
            [&](const typename Prize::PrizeHonor _args) -> T1 { return f; },
            [&](const typename Prize::PrizeEnclave _args) -> T1 {
              return f0(_args.d_a0);
            }},
        p->v());
  }

  template <typename T1, MapsTo<T1, unsigned int> F1>
  static T1 Prize_rec(const T1 f, F1 &&f0, const std::shared_ptr<Prize> &p) {
    return std::visit(
        Overloaded{
            [&](const typename Prize::PrizeHonor _args) -> T1 { return f; },
            [&](const typename Prize::PrizeEnclave _args) -> T1 {
              return f0(_args.d_a0);
            }},
        p->v());
  }

  struct Location {
    // TYPES
    struct LocPlanetSurface {
      unsigned int d_a0;
      unsigned int d_a1;
    };

    struct LocEnclave {
      unsigned int d_a0;
    };

    using variant_t = std::variant<LocPlanetSurface, LocEnclave>;

  private:
    // DATA
    variant_t d_v_;

    // CREATORS
    explicit Location(LocPlanetSurface _v) : d_v_(std::move(_v)) {}

    explicit Location(LocEnclave _v) : d_v_(std::move(_v)) {}

  public:
    // TYPES
    struct ctor {
      ctor() = delete;

      static std::shared_ptr<Location> LocPlanetSurface_(unsigned int a0,
                                                         unsigned int a1) {
        return std::shared_ptr<Location>(
            new Location(LocPlanetSurface{a0, a1}));
      }

      static std::shared_ptr<Location> LocEnclave_(unsigned int a0) {
        return std::shared_ptr<Location>(new Location(LocEnclave{a0}));
      }

      static std::unique_ptr<Location> LocPlanetSurface_uptr(unsigned int a0,
                                                             unsigned int a1) {
        return std::unique_ptr<Location>(
            new Location(LocPlanetSurface{a0, a1}));
      }

      static std::unique_ptr<Location> LocEnclave_uptr(unsigned int a0) {
        return std::unique_ptr<Location>(new Location(LocEnclave{a0}));
      }
    };

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, unsigned int, unsigned int> F0,
            MapsTo<T1, unsigned int> F1>
  static T1 Location_rect(F0 &&f, F1 &&f0, const std::shared_ptr<Location> &l) {
    return std::visit(
        Overloaded{[&](const typename Location::LocPlanetSurface _args) -> T1 {
                     return f(_args.d_a0, _args.d_a1);
                   },
                   [&](const typename Location::LocEnclave _args) -> T1 {
                     return f0(_args.d_a0);
                   }},
        l->v());
  }

  template <typename T1, MapsTo<T1, unsigned int, unsigned int> F0,
            MapsTo<T1, unsigned int> F1>
  static T1 Location_rec(F0 &&f, F1 &&f0, const std::shared_ptr<Location> &l) {
    return std::visit(
        Overloaded{[&](const typename Location::LocPlanetSurface _args) -> T1 {
                     return f(_args.d_a0, _args.d_a1);
                   },
                   [&](const typename Location::LocEnclave _args) -> T1 {
                     return f0(_args.d_a0);
                   }},
        l->v());
  }

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
      unsigned int d_a0;
    };

    using variant_t = std::variant<RefusalInsufficientRank, RefusalOther>;

  private:
    // DATA
    variant_t d_v_;

    // CREATORS
    explicit RefusalReason(RefusalInsufficientRank _v) : d_v_(std::move(_v)) {}

    explicit RefusalReason(RefusalOther _v) : d_v_(std::move(_v)) {}

  public:
    // TYPES
    struct ctor {
      ctor() = delete;

      static std::shared_ptr<RefusalReason> RefusalInsufficientRank_() {
        return std::shared_ptr<RefusalReason>(
            new RefusalReason(RefusalInsufficientRank{}));
      }

      static std::shared_ptr<RefusalReason> RefusalOther_(unsigned int a0) {
        return std::shared_ptr<RefusalReason>(
            new RefusalReason(RefusalOther{a0}));
      }

      static std::unique_ptr<RefusalReason> RefusalInsufficientRank_uptr() {
        return std::unique_ptr<RefusalReason>(
            new RefusalReason(RefusalInsufficientRank{}));
      }

      static std::unique_ptr<RefusalReason> RefusalOther_uptr(unsigned int a0) {
        return std::unique_ptr<RefusalReason>(
            new RefusalReason(RefusalOther{a0}));
      }
    };

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, unsigned int> F1>
  static T1 RefusalReason_rect(const T1 f, F1 &&f0,
                               const std::shared_ptr<RefusalReason> &r) {
    return std::visit(
        Overloaded{
            [&](const typename RefusalReason::RefusalInsufficientRank _args)
                -> T1 { return f; },
            [&](const typename RefusalReason::RefusalOther _args) -> T1 {
              return f0(_args.d_a0);
            }},
        r->v());
  }

  template <typename T1, MapsTo<T1, unsigned int> F1>
  static T1 RefusalReason_rec(const T1 f, F1 &&f0,
                              const std::shared_ptr<RefusalReason> &r) {
    return std::visit(
        Overloaded{
            [&](const typename RefusalReason::RefusalInsufficientRank _args)
                -> T1 { return f; },
            [&](const typename RefusalReason::RefusalOther _args) -> T1 {
              return f0(_args.d_a0);
            }},
        r->v());
  }

  struct ProtocolAction {
    // TYPES
    struct ActChallenge {
      std::shared_ptr<BatchallChallenge> d_a0;
    };

    struct ActRespond {
      std::shared_ptr<BatchallResponse> d_a0;
    };

    struct ActRefuse {
      std::shared_ptr<RefusalReason> d_a0;
    };

    struct ActBid {
      std::shared_ptr<ForceBid> d_a0;
    };

    struct ActCoalitionBid {
      std::shared_ptr<CoalitionMemberBid> d_a0;
    };

    struct ActPass {
      Side d_a0;
    };

    struct ActClose {};

    struct ActWithdraw {
      Side d_a0;
    };

    struct ActBreakBid {
      Side d_a0;
    };

    using variant_t = std::variant<ActChallenge, ActRespond, ActRefuse, ActBid,
                                   ActCoalitionBid, ActPass, ActClose,
                                   ActWithdraw, ActBreakBid>;

  private:
    // DATA
    variant_t d_v_;

    // CREATORS
    explicit ProtocolAction(ActChallenge _v) : d_v_(std::move(_v)) {}

    explicit ProtocolAction(ActRespond _v) : d_v_(std::move(_v)) {}

    explicit ProtocolAction(ActRefuse _v) : d_v_(std::move(_v)) {}

    explicit ProtocolAction(ActBid _v) : d_v_(std::move(_v)) {}

    explicit ProtocolAction(ActCoalitionBid _v) : d_v_(std::move(_v)) {}

    explicit ProtocolAction(ActPass _v) : d_v_(std::move(_v)) {}

    explicit ProtocolAction(ActClose _v) : d_v_(std::move(_v)) {}

    explicit ProtocolAction(ActWithdraw _v) : d_v_(std::move(_v)) {}

    explicit ProtocolAction(ActBreakBid _v) : d_v_(std::move(_v)) {}

  public:
    // TYPES
    struct ctor {
      ctor() = delete;

      static std::shared_ptr<ProtocolAction>
      ActChallenge_(const std::shared_ptr<BatchallChallenge> &a0) {
        return std::shared_ptr<ProtocolAction>(
            new ProtocolAction(ActChallenge{a0}));
      }

      static std::shared_ptr<ProtocolAction>
      ActRespond_(const std::shared_ptr<BatchallResponse> &a0) {
        return std::shared_ptr<ProtocolAction>(
            new ProtocolAction(ActRespond{a0}));
      }

      static std::shared_ptr<ProtocolAction>
      ActRefuse_(const std::shared_ptr<RefusalReason> &a0) {
        return std::shared_ptr<ProtocolAction>(
            new ProtocolAction(ActRefuse{a0}));
      }

      static std::shared_ptr<ProtocolAction>
      ActBid_(const std::shared_ptr<ForceBid> &a0) {
        return std::shared_ptr<ProtocolAction>(new ProtocolAction(ActBid{a0}));
      }

      static std::shared_ptr<ProtocolAction>
      ActCoalitionBid_(const std::shared_ptr<CoalitionMemberBid> &a0) {
        return std::shared_ptr<ProtocolAction>(
            new ProtocolAction(ActCoalitionBid{a0}));
      }

      static std::shared_ptr<ProtocolAction> ActPass_(Side a0) {
        return std::shared_ptr<ProtocolAction>(new ProtocolAction(ActPass{a0}));
      }

      static std::shared_ptr<ProtocolAction> ActClose_() {
        return std::shared_ptr<ProtocolAction>(new ProtocolAction(ActClose{}));
      }

      static std::shared_ptr<ProtocolAction> ActWithdraw_(Side a0) {
        return std::shared_ptr<ProtocolAction>(
            new ProtocolAction(ActWithdraw{a0}));
      }

      static std::shared_ptr<ProtocolAction> ActBreakBid_(Side a0) {
        return std::shared_ptr<ProtocolAction>(
            new ProtocolAction(ActBreakBid{a0}));
      }

      static std::unique_ptr<ProtocolAction>
      ActChallenge_uptr(const std::shared_ptr<BatchallChallenge> &a0) {
        return std::unique_ptr<ProtocolAction>(
            new ProtocolAction(ActChallenge{a0}));
      }

      static std::unique_ptr<ProtocolAction>
      ActRespond_uptr(const std::shared_ptr<BatchallResponse> &a0) {
        return std::unique_ptr<ProtocolAction>(
            new ProtocolAction(ActRespond{a0}));
      }

      static std::unique_ptr<ProtocolAction>
      ActRefuse_uptr(const std::shared_ptr<RefusalReason> &a0) {
        return std::unique_ptr<ProtocolAction>(
            new ProtocolAction(ActRefuse{a0}));
      }

      static std::unique_ptr<ProtocolAction>
      ActBid_uptr(const std::shared_ptr<ForceBid> &a0) {
        return std::unique_ptr<ProtocolAction>(new ProtocolAction(ActBid{a0}));
      }

      static std::unique_ptr<ProtocolAction>
      ActCoalitionBid_uptr(const std::shared_ptr<CoalitionMemberBid> &a0) {
        return std::unique_ptr<ProtocolAction>(
            new ProtocolAction(ActCoalitionBid{a0}));
      }

      static std::unique_ptr<ProtocolAction> ActPass_uptr(Side a0) {
        return std::unique_ptr<ProtocolAction>(new ProtocolAction(ActPass{a0}));
      }

      static std::unique_ptr<ProtocolAction> ActClose_uptr() {
        return std::unique_ptr<ProtocolAction>(new ProtocolAction(ActClose{}));
      }

      static std::unique_ptr<ProtocolAction> ActWithdraw_uptr(Side a0) {
        return std::unique_ptr<ProtocolAction>(
            new ProtocolAction(ActWithdraw{a0}));
      }

      static std::unique_ptr<ProtocolAction> ActBreakBid_uptr(Side a0) {
        return std::unique_ptr<ProtocolAction>(
            new ProtocolAction(ActBreakBid{a0}));
      }
    };

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
    return std::visit(
        Overloaded{
            [&](const typename ProtocolAction::ActChallenge _args) -> T1 {
              return f(_args.d_a0);
            },
            [&](const typename ProtocolAction::ActRespond _args) -> T1 {
              return f0(_args.d_a0);
            },
            [&](const typename ProtocolAction::ActRefuse _args) -> T1 {
              return f1(_args.d_a0);
            },
            [&](const typename ProtocolAction::ActBid _args) -> T1 {
              return f2(_args.d_a0);
            },
            [&](const typename ProtocolAction::ActCoalitionBid _args) -> T1 {
              return f3(_args.d_a0);
            },
            [&](const typename ProtocolAction::ActPass _args) -> T1 {
              return f4(_args.d_a0);
            },
            [&](const typename ProtocolAction::ActClose _args) -> T1 {
              return f5;
            },
            [&](const typename ProtocolAction::ActWithdraw _args) -> T1 {
              return f6(_args.d_a0);
            },
            [&](const typename ProtocolAction::ActBreakBid _args) -> T1 {
              return f7(_args.d_a0);
            }},
        p->v());
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
    return std::visit(
        Overloaded{
            [&](const typename ProtocolAction::ActChallenge _args) -> T1 {
              return f(_args.d_a0);
            },
            [&](const typename ProtocolAction::ActRespond _args) -> T1 {
              return f0(_args.d_a0);
            },
            [&](const typename ProtocolAction::ActRefuse _args) -> T1 {
              return f1(_args.d_a0);
            },
            [&](const typename ProtocolAction::ActBid _args) -> T1 {
              return f2(_args.d_a0);
            },
            [&](const typename ProtocolAction::ActCoalitionBid _args) -> T1 {
              return f3(_args.d_a0);
            },
            [&](const typename ProtocolAction::ActPass _args) -> T1 {
              return f4(_args.d_a0);
            },
            [&](const typename ProtocolAction::ActClose _args) -> T1 {
              return f5;
            },
            [&](const typename ProtocolAction::ActWithdraw _args) -> T1 {
              return f6(_args.d_a0);
            },
            [&](const typename ProtocolAction::ActBreakBid _args) -> T1 {
              return f7(_args.d_a0);
            }},
        p->v());
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
    return [&](void) {
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
      }
    }();
  }

  template <typename T1>
  static T1 ReadyStatus_rec(const T1 f, const T1 f0, const T1 f1, const T1 f2,
                            const ReadyStatus r) {
    return [&](void) {
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
      }
    }();
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

  struct BatchallPhase {
    // TYPES
    struct PhaseIdle {};

    struct PhaseChallenged {
      std::shared_ptr<BatchallChallenge> d_a0;
    };

    struct PhaseResponded {
      std::shared_ptr<BatchallChallenge> d_a0;
      std::shared_ptr<BatchallResponse> d_a1;
    };

    struct PhaseBidding {
      std::shared_ptr<BatchallChallenge> d_a0;
      std::shared_ptr<BatchallResponse> d_a1;
      std::shared_ptr<ForceBid> d_a2;
      std::shared_ptr<ForceBid> d_a3;
      CoalitionState d_a4;
      CoalitionState d_a5;
      std::shared_ptr<List<std::shared_ptr<ForceBid>>> d_a6;
      ReadyStatus d_a7;
    };

    struct PhaseAgreed {
      std::shared_ptr<BatchallChallenge> d_a0;
      std::shared_ptr<BatchallResponse> d_a1;
      std::shared_ptr<ForceBid> d_a2;
      std::shared_ptr<ForceBid> d_a3;
    };

    struct PhaseRefused {
      std::shared_ptr<BatchallChallenge> d_a0;
      std::shared_ptr<RefusalReason> d_a1;
    };

    struct PhaseAborted {
      std::shared_ptr<ProtocolAction> d_a0;
    };

    using variant_t =
        std::variant<PhaseIdle, PhaseChallenged, PhaseResponded, PhaseBidding,
                     PhaseAgreed, PhaseRefused, PhaseAborted>;

  private:
    // DATA
    variant_t d_v_;

    // CREATORS
    explicit BatchallPhase(PhaseIdle _v) : d_v_(std::move(_v)) {}

    explicit BatchallPhase(PhaseChallenged _v) : d_v_(std::move(_v)) {}

    explicit BatchallPhase(PhaseResponded _v) : d_v_(std::move(_v)) {}

    explicit BatchallPhase(PhaseBidding _v) : d_v_(std::move(_v)) {}

    explicit BatchallPhase(PhaseAgreed _v) : d_v_(std::move(_v)) {}

    explicit BatchallPhase(PhaseRefused _v) : d_v_(std::move(_v)) {}

    explicit BatchallPhase(PhaseAborted _v) : d_v_(std::move(_v)) {}

  public:
    // TYPES
    struct ctor {
      ctor() = delete;

      static std::shared_ptr<BatchallPhase> PhaseIdle_() {
        return std::shared_ptr<BatchallPhase>(new BatchallPhase(PhaseIdle{}));
      }

      static std::shared_ptr<BatchallPhase>
      PhaseChallenged_(const std::shared_ptr<BatchallChallenge> &a0) {
        return std::shared_ptr<BatchallPhase>(
            new BatchallPhase(PhaseChallenged{a0}));
      }

      static std::shared_ptr<BatchallPhase>
      PhaseResponded_(const std::shared_ptr<BatchallChallenge> &a0,
                      const std::shared_ptr<BatchallResponse> &a1) {
        return std::shared_ptr<BatchallPhase>(
            new BatchallPhase(PhaseResponded{a0, a1}));
      }

      static std::shared_ptr<BatchallPhase>
      PhaseBidding_(const std::shared_ptr<BatchallChallenge> &a0,
                    const std::shared_ptr<BatchallResponse> &a1,
                    const std::shared_ptr<ForceBid> &a2,
                    const std::shared_ptr<ForceBid> &a3, CoalitionState a4,
                    CoalitionState a5,
                    const std::shared_ptr<List<std::shared_ptr<ForceBid>>> &a6,
                    ReadyStatus a7) {
        return std::shared_ptr<BatchallPhase>(
            new BatchallPhase(PhaseBidding{a0, a1, a2, a3, a4, a5, a6, a7}));
      }

      static std::shared_ptr<BatchallPhase>
      PhaseAgreed_(const std::shared_ptr<BatchallChallenge> &a0,
                   const std::shared_ptr<BatchallResponse> &a1,
                   const std::shared_ptr<ForceBid> &a2,
                   const std::shared_ptr<ForceBid> &a3) {
        return std::shared_ptr<BatchallPhase>(
            new BatchallPhase(PhaseAgreed{a0, a1, a2, a3}));
      }

      static std::shared_ptr<BatchallPhase>
      PhaseRefused_(const std::shared_ptr<BatchallChallenge> &a0,
                    const std::shared_ptr<RefusalReason> &a1) {
        return std::shared_ptr<BatchallPhase>(
            new BatchallPhase(PhaseRefused{a0, a1}));
      }

      static std::shared_ptr<BatchallPhase>
      PhaseAborted_(const std::shared_ptr<ProtocolAction> &a0) {
        return std::shared_ptr<BatchallPhase>(
            new BatchallPhase(PhaseAborted{a0}));
      }

      static std::unique_ptr<BatchallPhase> PhaseIdle_uptr() {
        return std::unique_ptr<BatchallPhase>(new BatchallPhase(PhaseIdle{}));
      }

      static std::unique_ptr<BatchallPhase>
      PhaseChallenged_uptr(const std::shared_ptr<BatchallChallenge> &a0) {
        return std::unique_ptr<BatchallPhase>(
            new BatchallPhase(PhaseChallenged{a0}));
      }

      static std::unique_ptr<BatchallPhase>
      PhaseResponded_uptr(const std::shared_ptr<BatchallChallenge> &a0,
                          const std::shared_ptr<BatchallResponse> &a1) {
        return std::unique_ptr<BatchallPhase>(
            new BatchallPhase(PhaseResponded{a0, a1}));
      }

      static std::unique_ptr<BatchallPhase> PhaseBidding_uptr(
          const std::shared_ptr<BatchallChallenge> &a0,
          const std::shared_ptr<BatchallResponse> &a1,
          const std::shared_ptr<ForceBid> &a2,
          const std::shared_ptr<ForceBid> &a3, CoalitionState a4,
          CoalitionState a5,
          const std::shared_ptr<List<std::shared_ptr<ForceBid>>> &a6,
          ReadyStatus a7) {
        return std::unique_ptr<BatchallPhase>(
            new BatchallPhase(PhaseBidding{a0, a1, a2, a3, a4, a5, a6, a7}));
      }

      static std::unique_ptr<BatchallPhase>
      PhaseAgreed_uptr(const std::shared_ptr<BatchallChallenge> &a0,
                       const std::shared_ptr<BatchallResponse> &a1,
                       const std::shared_ptr<ForceBid> &a2,
                       const std::shared_ptr<ForceBid> &a3) {
        return std::unique_ptr<BatchallPhase>(
            new BatchallPhase(PhaseAgreed{a0, a1, a2, a3}));
      }

      static std::unique_ptr<BatchallPhase>
      PhaseRefused_uptr(const std::shared_ptr<BatchallChallenge> &a0,
                        const std::shared_ptr<RefusalReason> &a1) {
        return std::unique_ptr<BatchallPhase>(
            new BatchallPhase(PhaseRefused{a0, a1}));
      }

      static std::unique_ptr<BatchallPhase>
      PhaseAborted_uptr(const std::shared_ptr<ProtocolAction> &a0) {
        return std::unique_ptr<BatchallPhase>(
            new BatchallPhase(PhaseAborted{a0}));
      }
    };

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
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
    return std::visit(
        Overloaded{
            [&](const typename BatchallPhase::PhaseIdle _args) -> T1 {
              return f;
            },
            [&](const typename BatchallPhase::PhaseChallenged _args) -> T1 {
              return f0(_args.d_a0);
            },
            [&](const typename BatchallPhase::PhaseResponded _args) -> T1 {
              return f1(_args.d_a0, _args.d_a1);
            },
            [&](const typename BatchallPhase::PhaseBidding _args) -> T1 {
              return f2(_args.d_a0, _args.d_a1, _args.d_a2, _args.d_a3,
                        _args.d_a4, _args.d_a5, _args.d_a6, _args.d_a7);
            },
            [&](const typename BatchallPhase::PhaseAgreed _args) -> T1 {
              return f3(_args.d_a0, _args.d_a1, _args.d_a2, _args.d_a3);
            },
            [&](const typename BatchallPhase::PhaseRefused _args) -> T1 {
              return f4(_args.d_a0, _args.d_a1);
            },
            [&](const typename BatchallPhase::PhaseAborted _args) -> T1 {
              return f5(_args.d_a0);
            }},
        b->v());
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
    return std::visit(
        Overloaded{
            [&](const typename BatchallPhase::PhaseIdle _args) -> T1 {
              return f;
            },
            [&](const typename BatchallPhase::PhaseChallenged _args) -> T1 {
              return f0(_args.d_a0);
            },
            [&](const typename BatchallPhase::PhaseResponded _args) -> T1 {
              return f1(_args.d_a0, _args.d_a1);
            },
            [&](const typename BatchallPhase::PhaseBidding _args) -> T1 {
              return f2(_args.d_a0, _args.d_a1, _args.d_a2, _args.d_a3,
                        _args.d_a4, _args.d_a5, _args.d_a6, _args.d_a7);
            },
            [&](const typename BatchallPhase::PhaseAgreed _args) -> T1 {
              return f3(_args.d_a0, _args.d_a1, _args.d_a2, _args.d_a3);
            },
            [&](const typename BatchallPhase::PhaseRefused _args) -> T1 {
              return f4(_args.d_a0, _args.d_a1);
            },
            [&](const typename BatchallPhase::PhaseAborted _args) -> T1 {
              return f5(_args.d_a0);
            }},
        b->v());
  }

  __attribute__((pure)) static bool
  is_terminal(const std::shared_ptr<BatchallPhase> &phase);
  __attribute__((pure)) static bool
  is_bidding(const std::shared_ptr<BatchallPhase> &phase);
  __attribute__((pure)) static unsigned int
  phase_depth(const std::shared_ptr<BatchallPhase> &phase);
  __attribute__((pure)) static unsigned int
  get_bidding_measure(const std::shared_ptr<BatchallPhase> &phase);
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
  __attribute__((pure)) static std::optional<std::shared_ptr<Commander>>
  get_side_commander(const std::shared_ptr<BatchallPhase> &phase,
                     const Side side);
  __attribute__((pure)) static std::optional<std::shared_ptr<Commander>>
  action_actor_in_phase(const std::shared_ptr<BatchallPhase> &phase,
                        const std::shared_ptr<ProtocolAction> &action);

  struct BatchallState {
    std::shared_ptr<BatchallPhase> bs_phase;
    HonorLedger bs_honor;
  };

  static inline const HonorLedger empty_ledger =
      List<std::pair<unsigned int, std::shared_ptr<Z>>>::ctor::Nil_();
  static inline const std::shared_ptr<BatchallState> initial_state =
      std::make_shared<BatchallState>(
          BatchallState{BatchallPhase::ctor::PhaseIdle_(), empty_ledger});
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
  static inline const Force falcon_trinary =
      List<std::shared_ptr<Unit>>::ctor::Cons_(
          direwolf,
          List<std::shared_ptr<Unit>>::ctor::Cons_(
              timberwolf,
              List<std::shared_ptr<Unit>>::ctor::Cons_(
                  summoner,
                  List<std::shared_ptr<Unit>>::ctor::Cons_(
                      mad_dog, List<std::shared_ptr<Unit>>::ctor::Nil_()))));
  static inline const Force wolf_binary =
      List<std::shared_ptr<Unit>>::ctor::Cons_(
          timberwolf, List<std::shared_ptr<Unit>>::ctor::Cons_(
                          summoner, List<std::shared_ptr<Unit>>::ctor::Nil_()));
  static inline const Force bear_support =
      List<std::shared_ptr<Unit>>::ctor::Cons_(
          elementals,
          List<std::shared_ptr<Unit>>::ctor::Cons_(
              elementals, List<std::shared_ptr<Unit>>::ctor::Nil_()));
  static inline const Coalition attacker_coalition =
      List<std::shared_ptr<CoalitionMember>>::ctor::Cons_(
          std::make_shared<CoalitionMember>(
              CoalitionMember{Clan::e_CLANJADEFALCON, malthus, falcon_trinary}),
          List<std::shared_ptr<CoalitionMember>>::ctor::Cons_(
              std::make_shared<CoalitionMember>(CoalitionMember{
                  Clan::e_CLANGHOSTBEAR, bear_ally, bear_support}),
              List<std::shared_ptr<CoalitionMember>>::ctor::Nil_()));
  static inline const Coalition defender_coalition =
      List<std::shared_ptr<CoalitionMember>>::ctor::Cons_(
          std::make_shared<CoalitionMember>(
              CoalitionMember{Clan::e_CLANWOLF, radick, wolf_binary}),
          List<std::shared_ptr<CoalitionMember>>::ctor::Nil_());
  static inline const std::shared_ptr<BatchallChallenge> sample_challenge =
      std::make_shared<BatchallChallenge>(BatchallChallenge{
          malthus, Clan::e_CLANJADEFALCON, Prize::ctor::PrizeEnclave_(42u),
          coalition_force(attacker_coalition),
          Location::ctor::LocPlanetSurface_(7u, 3u),
          TrialType::e_TRIALOFPOSSESSION, standard_possession_context});
  static inline const std::shared_ptr<BatchallResponse> sample_response =
      std::make_shared<BatchallResponse>(BatchallResponse{
          radick, Clan::e_CLANWOLF, coalition_force(defender_coalition)});
  static inline const std::shared_ptr<ForceBid> sample_attacker_bid = [](void) {
    if (coalition_to_bid(attacker_coalition, Side::e_ATTACKER).has_value()) {
      std::shared_ptr<ForceBid> bid =
          *coalition_to_bid(attacker_coalition, Side::e_ATTACKER);
      return bid;
    } else {
      return std::make_shared<ForceBid>(
          ForceBid{List<std::shared_ptr<Unit>>::ctor::Nil_(), Side::e_ATTACKER,
                   malthus});
    }
  }();
  static inline const std::shared_ptr<ForceBid> sample_defender_bid = [](void) {
    if (coalition_to_bid(defender_coalition, Side::e_DEFENDER).has_value()) {
      std::shared_ptr<ForceBid> bid =
          *coalition_to_bid(defender_coalition, Side::e_DEFENDER);
      return bid;
    } else {
      return std::make_shared<ForceBid>(ForceBid{
          List<std::shared_ptr<Unit>>::ctor::Nil_(), Side::e_DEFENDER, radick});
    }
  }();
  static inline const Force reduced_support_force =
      List<std::shared_ptr<Unit>>::ctor::Cons_(
          elementals, List<std::shared_ptr<Unit>>::ctor::Nil_());
  static inline const std::shared_ptr<CoalitionMemberBid>
      sample_coalition_member_bid = std::make_shared<CoalitionMemberBid>(
          CoalitionMemberBid{1u, reduced_support_force, Side::e_ATTACKER});
  static inline const Coalition updated_attacker_coalition =
      apply_coalition_member_bid(attacker_coalition,
                                 sample_coalition_member_bid);
  static inline const std::shared_ptr<ForceBid> updated_attacker_bid =
      [](void) {
        if (coalition_to_bid(updated_attacker_coalition, Side::e_ATTACKER)
                .has_value()) {
          std::shared_ptr<ForceBid> bid =
              *coalition_to_bid(updated_attacker_coalition, Side::e_ATTACKER);
          return bid;
        } else {
          return sample_attacker_bid;
        }
      }();
  static inline const std::shared_ptr<BatchallPhase> phase_after_initial_bid =
      BatchallPhase::ctor::PhaseBidding_(
          sample_challenge, sample_response, sample_attacker_bid,
          sample_defender_bid,
          std::make_optional<
              std::shared_ptr<List<std::shared_ptr<CoalitionMember>>>>(
              attacker_coalition),
          std::make_optional<
              std::shared_ptr<List<std::shared_ptr<CoalitionMember>>>>(
              defender_coalition),
          List<std::shared_ptr<ForceBid>>::ctor::Nil_(),
          ReadyStatus::e_NEITHERREADY);
  static inline const std::shared_ptr<BatchallPhase> phase_after_attacker_pass =
      BatchallPhase::ctor::PhaseBidding_(
          sample_challenge, sample_response, sample_attacker_bid,
          sample_defender_bid,
          std::make_optional<
              std::shared_ptr<List<std::shared_ptr<CoalitionMember>>>>(
              attacker_coalition),
          std::make_optional<
              std::shared_ptr<List<std::shared_ptr<CoalitionMember>>>>(
              defender_coalition),
          List<std::shared_ptr<ForceBid>>::ctor::Nil_(),
          ReadyStatus::e_ATTACKERREADY);
  static inline const std::shared_ptr<BatchallPhase> phase_after_coalition_bid =
      BatchallPhase::ctor::PhaseBidding_(
          sample_challenge, sample_response, updated_attacker_bid,
          sample_defender_bid,
          std::make_optional<
              std::shared_ptr<List<std::shared_ptr<CoalitionMember>>>>(
              updated_attacker_coalition),
          std::make_optional<
              std::shared_ptr<List<std::shared_ptr<CoalitionMember>>>>(
              defender_coalition),
          List<std::shared_ptr<ForceBid>>::ctor::Cons_(
              sample_attacker_bid,
              List<std::shared_ptr<ForceBid>>::ctor::Nil_()),
          ReadyStatus::e_NEITHERREADY);
  static inline const std::shared_ptr<BatchallPhase> phase_agreed =
      BatchallPhase::ctor::PhaseAgreed_(sample_challenge, sample_response,
                                        updated_attacker_bid,
                                        sample_defender_bid);
  static inline const std::shared_ptr<BatchallState> state_after_initial_bid =
      std::make_shared<BatchallState>(
          BatchallState{phase_after_initial_bid, empty_ledger});
  static inline const HonorLedger sample_challenge_honor_ledger =
      apply_action_honor(initial_state,
                         ProtocolAction::ctor::ActChallenge_(sample_challenge));
  static inline const HonorLedger sample_break_bid_honor_ledger =
      apply_action_honor(state_after_initial_bid,
                         ProtocolAction::ctor::ActBreakBid_(Side::e_ATTACKER));
  static inline const bool sample_challenger_may_issue =
      may_issue_batchall(malthus);
  static inline const bool sample_coalition_bid_is_valid =
      valid_coalition_member_bid_b(attacker_coalition,
                                   sample_coalition_member_bid);
  static inline const bool sample_coalition_contains_bear =
      coalition_contains_clan(attacker_coalition, Clan::e_CLANGHOSTBEAR);
  static inline const bool sample_updated_tonnage_reduced =
      PeanoNat::ltb(coalition_tonnage(updated_attacker_coalition),
                    coalition_tonnage(attacker_coalition));
  static inline const bool sample_attacker_ready_after_pass =
      is_ready(set_ready(ReadyStatus::e_NEITHERREADY, Side::e_ATTACKER),
               Side::e_ATTACKER);
  static inline const bool sample_attacker_not_ready_after_clear =
      !(is_ready(clear_ready(ReadyStatus::e_BOTHREADY, Side::e_ATTACKER),
                 Side::e_ATTACKER));
  static inline const bool sample_phase_is_bidding =
      is_bidding(phase_after_initial_bid);
  static inline const bool sample_agreed_terminal = is_terminal(phase_agreed);
  static inline const unsigned int sample_phase_depth_before_close =
      phase_depth(phase_after_initial_bid);
  static inline const unsigned int sample_phase_depth_after_close =
      phase_depth(phase_agreed);
  static inline const bool sample_bidding_measure_reduced =
      PeanoNat::ltb(get_bidding_measure(phase_after_coalition_bid),
                    get_bidding_measure(phase_after_initial_bid));
  static inline const Honor sample_challenge_honor =
      ledger_lookup(sample_challenge_honor_ledger, malthus->cmd_id);
  static inline const Honor sample_break_bid_honor =
      ledger_lookup(sample_break_bid_honor_ledger, malthus->cmd_id);
  static inline const bool sample_challenge_honor_is_one = BinInt::eqb(
      sample_challenge_honor, Z::ctor::Zpos_(Positive::ctor::XH_()));
  static inline const bool sample_break_bid_honor_is_minus_ten =
      BinInt::eqb(sample_break_bid_honor,
                  Z::ctor::Zneg_(Positive::ctor::XO_(Positive::ctor::XI_(
                      Positive::ctor::XO_(Positive::ctor::XH_())))));
  static inline const unsigned int sample_break_bid_actor_id = [](void) {
    if (action_actor_in_phase(
            phase_after_initial_bid,
            ProtocolAction::ctor::ActBreakBid_(Side::e_ATTACKER))
            .has_value()) {
      std::shared_ptr<Commander> cmd = *action_actor_in_phase(
          phase_after_initial_bid,
          ProtocolAction::ctor::ActBreakBid_(Side::e_ATTACKER));
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
          List<std::shared_ptr<Unit>>::ctor::Nil_())
          ->length();
};

#endif // INCLUDED_COALITION_BID_HONOR_TRACE
