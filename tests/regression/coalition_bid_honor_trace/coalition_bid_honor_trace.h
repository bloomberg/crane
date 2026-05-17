#ifndef INCLUDED_COALITION_BID_HONOR_TRACE
#define INCLUDED_COALITION_BID_HONOR_TRACE

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

template <typename A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    A a0;
    std::unique_ptr<List<A>> a1;
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

  List(const List<A> &_other) : v_(std::move(_other.clone().v_)) {}

  List(List<A> &&_other) noexcept : v_(std::move(_other.v_)) {}

  List<A> &operator=(const List<A> &_other) {
    v_ = std::move(_other.clone().v_);
    return *this;
  }

  List<A> &operator=(List<A> &&_other) noexcept {
    v_ = std::move(_other.v_);
    return *this;
  }

  // ACCESSORS
  List<A> clone() const {
    List<A> _out{};

    struct _CloneFrame {
      const List<A> *_src;
      List<A> *_dst;
    };

    std::vector<_CloneFrame> _stack{};
    _stack.reserve(8);
    _stack.push_back({this, &_out});
    while (!_stack.empty()) {
      auto _frame = _stack.back();
      _stack.pop_back();
      const List<A> *_src = _frame._src;
      List<A> *_dst = _frame._dst;
      if (std::holds_alternative<Nil>(_src->v())) {
        _dst->v_ = Nil{};
      } else {
        const auto &_alt = std::get<Cons>(_src->v());
        _dst->v_ =
            Cons{_alt.a0, _alt.a1 ? std::make_unique<List<A>>() : nullptr};
        auto &_dst_alt = std::get<Cons>(_dst->v_);
        if (_alt.a1) {
          _stack.push_back({_alt.a1.get(), _dst_alt.a1.get()});
        }
      }
    }
    return _out;
  }

  // CREATORS
  template <typename _U> explicit List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      this->v_ = Nil{};
    } else {
      const auto &[a0, a1] = std::get<typename List<_U>::Cons>(_other.v());
      this->v_ = Cons{A(a0), a1 ? std::make_unique<List<A>>(*a1) : nullptr};
    }
  }

  static List<A> nil() { return List(Nil{}); }

  static List<A> cons(A a0, List<A> a1) {
    return List(Cons{std::move(a0), std::make_unique<List<A>>(std::move(a1))});
  }

  // MANIPULATORS
  ~List() {
    std::vector<std::unique_ptr<List<A>>> _stack{};
    _stack.reserve(8);
    auto _drain = [&](List<A> &_node) {
      if (std::holds_alternative<Cons>(_node.v_)) {
        auto &_alt = std::get<Cons>(_node.v_);
        if (_alt.a1) {
          _stack.push_back(std::move(_alt.a1));
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

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  template <typename F0>
    requires std::is_invocable_r_v<bool, F0 &, A &>
  bool existsb(F0 &&f) const {
    if (std::holds_alternative<typename List<A>::Nil>(this->v())) {
      return false;
    } else {
      const auto &[a0, a1] = std::get<typename List<A>::Cons>(this->v());
      return (f(a0) || (*a1).existsb(f));
    }
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, A &, T1 &>
  T1 fold_right(F0 &&f, T1 a0) const {
    if (std::holds_alternative<typename List<A>::Nil>(this->v())) {
      return a0;
    } else {
      const auto &[a1, a2] = std::get<typename List<A>::Cons>(this->v());
      return f(a1, (*a2).template fold_right<T1>(f, a0));
    }
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<List<T1>, F0 &, A &>
  List<T1> flat_map(F0 &&f) const {
    if (std::holds_alternative<typename List<A>::Nil>(this->v())) {
      return List<T1>::nil();
    } else {
      const auto &[a0, a1] = std::get<typename List<A>::Cons>(this->v());
      return f(a0).app((*a1).template flat_map<T1>(f));
    }
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, A &>
  List<T1> map(F0 &&f) const {
    if (std::holds_alternative<typename List<A>::Nil>(this->v())) {
      return List<T1>::nil();
    } else {
      const auto &[a0, a1] = std::get<typename List<A>::Cons>(this->v());
      return List<T1>::cons(f(a0), (*a1).template map<T1>(f));
    }
  }

  unsigned int length() const {
    if (std::holds_alternative<typename List<A>::Nil>(this->v())) {
      return 0u;
    } else {
      const auto &[a0, a1] = std::get<typename List<A>::Cons>(this->v());
      return ((*a1).length() + 1);
    }
  }

  List<A> app(List<A> m) const {
    if (std::holds_alternative<typename List<A>::Nil>(this->v())) {
      return m;
    } else {
      const auto &[a0, a1] = std::get<typename List<A>::Cons>(this->v());
      return List<A>::cons(a0, (*a1).app(std::move(m)));
    }
  }
};

struct Positive {
  // TYPES
  struct XI {
    std::unique_ptr<Positive> a0;
  };

  struct XO {
    std::unique_ptr<Positive> a0;
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

  Positive(const Positive &_other) : v_(std::move(_other.clone().v_)) {}

  Positive(Positive &&_other) noexcept : v_(std::move(_other.v_)) {}

  Positive &operator=(const Positive &_other) {
    v_ = std::move(_other.clone().v_);
    return *this;
  }

  Positive &operator=(Positive &&_other) noexcept {
    v_ = std::move(_other.v_);
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
    _stack.reserve(8);
    _stack.push_back({this, &_out});
    while (!_stack.empty()) {
      auto _frame = _stack.back();
      _stack.pop_back();
      const Positive *_src = _frame._src;
      Positive *_dst = _frame._dst;
      if (std::holds_alternative<XI>(_src->v())) {
        const auto &_alt = std::get<XI>(_src->v());
        _dst->v_ = XI{_alt.a0 ? std::make_unique<Positive>() : nullptr};
        auto &_dst_alt = std::get<XI>(_dst->v_);
        if (_alt.a0) {
          _stack.push_back({_alt.a0.get(), _dst_alt.a0.get()});
        }
      } else if (std::holds_alternative<XO>(_src->v())) {
        const auto &_alt = std::get<XO>(_src->v());
        _dst->v_ = XO{_alt.a0 ? std::make_unique<Positive>() : nullptr};
        auto &_dst_alt = std::get<XO>(_dst->v_);
        if (_alt.a0) {
          _stack.push_back({_alt.a0.get(), _dst_alt.a0.get()});
        }
      } else {
        _dst->v_ = XH{};
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
    _stack.reserve(8);
    auto _drain = [&](Positive &_node) {
      if (std::holds_alternative<XI>(_node.v_)) {
        auto &_alt = std::get<XI>(_node.v_);
        if (_alt.a0) {
          _stack.push_back(std::move(_alt.a0));
        }
      }
      if (std::holds_alternative<XO>(_node.v_)) {
        auto &_alt = std::get<XO>(_node.v_);
        if (_alt.a0) {
          _stack.push_back(std::move(_alt.a0));
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

  Z(const Z &_other) : v_(std::move(_other.clone().v_)) {}

  Z(Z &&_other) noexcept : v_(std::move(_other.v_)) {}

  Z &operator=(const Z &_other) {
    v_ = std::move(_other.clone().v_);
    return *this;
  }

  Z &operator=(Z &&_other) noexcept {
    v_ = std::move(_other.v_);
    return *this;
  }

  // ACCESSORS
  Z clone() const {
    if (std::holds_alternative<Z0>(this->v())) {
      return Z(Z0{});
    } else if (std::holds_alternative<Zpos>(this->v())) {
      const auto &[a0] = std::get<Zpos>(this->v());
      return Z(Zpos{a0.clone()});
    } else {
      const auto &[a0] = std::get<Zneg>(this->v());
      return Z(Zneg{a0.clone()});
    }
  }

  // CREATORS
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
  static bool eqb(const Positive &p, const Positive &q);
};

struct BinInt {
  static Z double_(const Z &x);
  static Z succ_double(const Z &x);
  static Z pred_double(const Z &x);
  static Z pos_sub(const Positive &x, const Positive &y);
  static Z add(Z x, Z y);
  static bool eqb(const Z &x, const Z &y);
};

struct ListDef {
  template <typename T1>
  static T1 nth(unsigned int n, const List<T1> &l, T1 default0);
};

struct CoalitionBidHonorTraceCase {
  enum class Clan { CLANWOLF, CLANJADEFALCON, CLANGHOSTBEAR };

  template <typename T1> static T1 Clan_rect(T1 f, T1 f0, T1 f1, Clan c) {
    switch (c) {
    case Clan::CLANWOLF: {
      return f;
    }
    case Clan::CLANJADEFALCON: {
      return f0;
    }
    case Clan::CLANGHOSTBEAR: {
      return f1;
    }
    default:
      std::unreachable();
    }
  }

  template <typename T1> static T1 Clan_rec(T1 f, T1 f0, T1 f1, Clan c) {
    switch (c) {
    case Clan::CLANWOLF: {
      return f;
    }
    case Clan::CLANJADEFALCON: {
      return f0;
    }
    case Clan::CLANGHOSTBEAR: {
      return f1;
    }
    default:
      std::unreachable();
    }
  }

  static bool clan_eq_dec(Clan c1, Clan c2);
  static bool clan_eqb(Clan c1, Clan c2);
  enum class Rank { WARRIOR, STARCAPTAIN, STARCOLONEL };

  template <typename T1> static T1 Rank_rect(T1 f, T1 f0, T1 f1, Rank r) {
    switch (r) {
    case Rank::WARRIOR: {
      return f;
    }
    case Rank::STARCAPTAIN: {
      return f0;
    }
    case Rank::STARCOLONEL: {
      return f1;
    }
    default:
      std::unreachable();
    }
  }

  template <typename T1> static T1 Rank_rec(T1 f, T1 f0, T1 f1, Rank r) {
    switch (r) {
    case Rank::WARRIOR: {
      return f;
    }
    case Rank::STARCAPTAIN: {
      return f0;
    }
    case Rank::STARCOLONEL: {
      return f1;
    }
    default:
      std::unreachable();
    }
  }

  static unsigned int rank_to_nat(Rank r);
  static bool rank_le(Rank r1, Rank r2);

  struct Commander {
    unsigned int cmd_id;
    Clan cmd_clan;
    Rank cmd_rank;
    bool cmd_bloodnamed;

    // ACCESSORS
    Commander clone() const {
      return Commander{(*this).cmd_id, (*this).cmd_clan, (*this).cmd_rank,
                       (*this).cmd_bloodnamed};
    }
  };

  static bool may_issue_batchall(const Commander &c);
  enum class UnitClass { OMNIMECH, BATTLEMECH, ELEMENTAL };

  template <typename T1>
  static T1 UnitClass_rect(T1 f, T1 f0, T1 f1, UnitClass u) {
    switch (u) {
    case UnitClass::OMNIMECH: {
      return f;
    }
    case UnitClass::BATTLEMECH: {
      return f0;
    }
    case UnitClass::ELEMENTAL: {
      return f1;
    }
    default:
      std::unreachable();
    }
  }

  template <typename T1>
  static T1 UnitClass_rec(T1 f, T1 f0, T1 f1, UnitClass u) {
    switch (u) {
    case UnitClass::OMNIMECH: {
      return f;
    }
    case UnitClass::BATTLEMECH: {
      return f0;
    }
    case UnitClass::ELEMENTAL: {
      return f1;
    }
    default:
      std::unreachable();
    }
  }
  enum class WeightClass { LIGHT, HEAVY, ASSAULT };

  template <typename T1>
  static T1 WeightClass_rect(T1 f, T1 f0, T1 f1, WeightClass w) {
    switch (w) {
    case WeightClass::LIGHT: {
      return f;
    }
    case WeightClass::HEAVY: {
      return f0;
    }
    case WeightClass::ASSAULT: {
      return f1;
    }
    default:
      std::unreachable();
    }
  }

  template <typename T1>
  static T1 WeightClass_rec(T1 f, T1 f0, T1 f1, WeightClass w) {
    switch (w) {
    case WeightClass::LIGHT: {
      return f;
    }
    case WeightClass::HEAVY: {
      return f0;
    }
    case WeightClass::ASSAULT: {
      return f1;
    }
    default:
      std::unreachable();
    }
  }

  static unsigned int weight_class_value(WeightClass w);
  static unsigned int unit_class_bonus(UnitClass c);

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
    Unit clone() const {
      return Unit{(*this).unit_id,       (*this).unit_class,
                  (*this).unit_weight,   (*this).unit_tonnage,
                  (*this).unit_gunnery,  (*this).unit_piloting,
                  (*this).unit_is_elite, (*this).unit_is_clan};
    }
  };

  static unsigned int unit_skill(const Unit &u);
  static unsigned int skill_bv_multiplier_num(unsigned int skill);
  static unsigned int unit_base_bv(const Unit &u);
  static unsigned int unit_tech_bv(const Unit &u);
  static unsigned int unit_battle_value(const Unit &u);
  static unsigned int unit_effective_combat_rating(const Unit &u);
  using Force = List<Unit>;

  struct ForceMetrics {
    unsigned int fm_count;
    unsigned int fm_tonnage;
    unsigned int fm_elite_count;
    unsigned int fm_clan_count;
    unsigned int fm_total_bv;
    unsigned int fm_total_ecr;

    // ACCESSORS
    ForceMetrics clone() const {
      return ForceMetrics{(*this).fm_count,       (*this).fm_tonnage,
                          (*this).fm_elite_count, (*this).fm_clan_count,
                          (*this).fm_total_bv,    (*this).fm_total_ecr};
    }
  };

  static inline const ForceMetrics empty_metrics =
      ForceMetrics{0u, 0u, 0u, 0u, 0u, 0u};
  static ForceMetrics unit_to_metrics(const Unit &u);
  static ForceMetrics metrics_add(const ForceMetrics &m1,
                                  const ForceMetrics &m2);
  static ForceMetrics force_metrics(const List<Unit> &f);
  static bool metrics_total_lt(const ForceMetrics &m1, const ForceMetrics &m2);
  enum class Side { ATTACKER, DEFENDER };

  template <typename T1> static T1 Side_rect(T1 f, T1 f0, Side s) {
    switch (s) {
    case Side::ATTACKER: {
      return f;
    }
    case Side::DEFENDER: {
      return f0;
    }
    default:
      std::unreachable();
    }
  }

  template <typename T1> static T1 Side_rec(T1 f, T1 f0, Side s) {
    switch (s) {
    case Side::ATTACKER: {
      return f;
    }
    case Side::DEFENDER: {
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
    CoalitionMember clone() const {
      return CoalitionMember{(*this).cm_clan, (*this).cm_commander.clone(),
                             (*this).cm_force};
    }
  };

  using Coalition = List<CoalitionMember>;
  static Force coalition_force(const List<CoalitionMember> &c);
  static ForceMetrics coalition_metrics(const List<CoalitionMember> &c);
  static bool coalition_contains_clan(const List<CoalitionMember> &c,
                                      Clan clan);
  static unsigned int coalition_tonnage(const List<CoalitionMember> &c);

  struct CoalitionMemberBid {
    unsigned int cmb_member_index;
    Force cmb_new_force;
    Side cmb_side;

    // ACCESSORS
    CoalitionMemberBid clone() const {
      return CoalitionMemberBid{(*this).cmb_member_index, (*this).cmb_new_force,
                                (*this).cmb_side};
    }
  };

  static Coalition update_coalition_force(const List<CoalitionMember> &c,
                                          unsigned int idx,
                                          List<Unit> new_force);

  struct ForceBid {
    Force bid_force;
    Side bid_side;
    Commander bid_commander;

    // ACCESSORS
    ForceBid clone() const {
      return ForceBid{(*this).bid_force, (*this).bid_side,
                      (*this).bid_commander.clone()};
    }
  };

  static ForceMetrics bid_metrics(const ForceBid &b);
  static std::optional<Commander>
  coalition_lead_commander(const List<CoalitionMember> &c);
  static std::optional<ForceBid>
  coalition_to_bid(const List<CoalitionMember> &c, Side side);
  static Coalition apply_coalition_member_bid(const List<CoalitionMember> &c,
                                              const CoalitionMemberBid &cbid);
  static bool valid_coalition_member_bid_b(const List<CoalitionMember> &c,
                                           const CoalitionMemberBid &cbid);
  enum class TrialType { TRIALOFPOSSESSION, TRIALOFANNIHILATION };

  template <typename T1> static T1 TrialType_rect(T1 f, T1 f0, TrialType t) {
    switch (t) {
    case TrialType::TRIALOFPOSSESSION: {
      return f;
    }
    case TrialType::TRIALOFANNIHILATION: {
      return f0;
    }
    default:
      std::unreachable();
    }
  }

  template <typename T1> static T1 TrialType_rec(T1 f, T1 f0, TrialType t) {
    switch (t) {
    case TrialType::TRIALOFPOSSESSION: {
      return f;
    }
    case TrialType::TRIALOFANNIHILATION: {
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
      unsigned int enclave_id;
    };

    using variant_t = std::variant<PrizeHonor, PrizeEnclave>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    Prize() {}

    explicit Prize(PrizeHonor _v) : v_(_v) {}

    explicit Prize(PrizeEnclave _v) : v_(std::move(_v)) {}

    Prize(const Prize &_other) : v_(std::move(_other.clone().v_)) {}

    Prize(Prize &&_other) noexcept : v_(std::move(_other.v_)) {}

    Prize &operator=(const Prize &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    Prize &operator=(Prize &&_other) noexcept {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    Prize clone() const {
      if (std::holds_alternative<PrizeHonor>(this->v())) {
        return Prize(PrizeHonor{});
      } else {
        const auto &[enclave_id] = std::get<PrizeEnclave>(this->v());
        return Prize(PrizeEnclave{enclave_id});
      }
    }

    // CREATORS
    static Prize prizehonor() { return Prize(PrizeHonor{}); }

    static Prize prizeenclave(unsigned int enclave_id) {
      return Prize(PrizeEnclave{enclave_id});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, unsigned int &>
    T1 Prize_rec(T1 f, F1 &&f0) const {
      if (std::holds_alternative<typename Prize::PrizeHonor>(this->v())) {
        return f;
      } else {
        const auto &[enclave_id0] =
            std::get<typename Prize::PrizeEnclave>(this->v());
        return f0(enclave_id0);
      }
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, unsigned int &>
    T1 Prize_rect(T1 f, F1 &&f0) const {
      if (std::holds_alternative<typename Prize::PrizeHonor>(this->v())) {
        return f;
      } else {
        const auto &[enclave_id0] =
            std::get<typename Prize::PrizeEnclave>(this->v());
        return f0(enclave_id0);
      }
    }
  };

  struct Location {
    // TYPES
    struct LocPlanetSurface {
      unsigned int world_id;
      unsigned int region_id;
    };

    struct LocEnclave {
      unsigned int enclave_id;
    };

    using variant_t = std::variant<LocPlanetSurface, LocEnclave>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    Location() {}

    explicit Location(LocPlanetSurface _v) : v_(std::move(_v)) {}

    explicit Location(LocEnclave _v) : v_(std::move(_v)) {}

    Location(const Location &_other) : v_(std::move(_other.clone().v_)) {}

    Location(Location &&_other) noexcept : v_(std::move(_other.v_)) {}

    Location &operator=(const Location &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    Location &operator=(Location &&_other) noexcept {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    Location clone() const {
      if (std::holds_alternative<LocPlanetSurface>(this->v())) {
        const auto &[world_id, region_id] =
            std::get<LocPlanetSurface>(this->v());
        return Location(LocPlanetSurface{world_id, region_id});
      } else {
        const auto &[enclave_id] = std::get<LocEnclave>(this->v());
        return Location(LocEnclave{enclave_id});
      }
    }

    // CREATORS
    static Location locplanetsurface(unsigned int world_id,
                                     unsigned int region_id) {
      return Location(LocPlanetSurface{world_id, region_id});
    }

    static Location locenclave(unsigned int enclave_id) {
      return Location(LocEnclave{enclave_id});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    template <typename T1, typename F0, typename F1>
      requires std::is_invocable_r_v<T1, F0 &, unsigned int &,
                                     unsigned int &> &&
               std::is_invocable_r_v<T1, F1 &, unsigned int &>
    T1 Location_rec(F0 &&f, F1 &&f0) const {
      if (std::holds_alternative<typename Location::LocPlanetSurface>(
              this->v())) {
        const auto &[world_id0, region_id0] =
            std::get<typename Location::LocPlanetSurface>(this->v());
        return f(world_id0, region_id0);
      } else {
        const auto &[enclave_id0] =
            std::get<typename Location::LocEnclave>(this->v());
        return f0(enclave_id0);
      }
    }

    template <typename T1, typename F0, typename F1>
      requires std::is_invocable_r_v<T1, F0 &, unsigned int &,
                                     unsigned int &> &&
               std::is_invocable_r_v<T1, F1 &, unsigned int &>
    T1 Location_rect(F0 &&f, F1 &&f0) const {
      if (std::holds_alternative<typename Location::LocPlanetSurface>(
              this->v())) {
        const auto &[world_id0, region_id0] =
            std::get<typename Location::LocPlanetSurface>(this->v());
        return f(world_id0, region_id0);
      } else {
        const auto &[enclave_id0] =
            std::get<typename Location::LocEnclave>(this->v());
        return f0(enclave_id0);
      }
    }
  };

  struct BattleContext {
    bool ctx_hegira_allowed;
    bool ctx_circle_present;

    // ACCESSORS
    BattleContext clone() const {
      return BattleContext{(*this).ctx_hegira_allowed,
                           (*this).ctx_circle_present};
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
    BatchallChallenge clone() const {
      return BatchallChallenge{
          (*this).chal_challenger.clone(), (*this).chal_clan,
          (*this).chal_prize.clone(),      (*this).chal_initial_force,
          (*this).chal_location.clone(),   (*this).chal_trial_type,
          (*this).chal_context.clone()};
    }
  };

  struct BatchallResponse {
    Commander resp_defender;
    Clan resp_clan;
    Force resp_force;

    // ACCESSORS
    BatchallResponse clone() const {
      return BatchallResponse{(*this).resp_defender.clone(), (*this).resp_clan,
                              (*this).resp_force};
    }
  };

  struct RefusalReason {
    // TYPES
    struct RefusalInsufficientRank {};

    struct RefusalOther {
      unsigned int note;
    };

    using variant_t = std::variant<RefusalInsufficientRank, RefusalOther>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    RefusalReason() {}

    explicit RefusalReason(RefusalInsufficientRank _v) : v_(_v) {}

    explicit RefusalReason(RefusalOther _v) : v_(std::move(_v)) {}

    RefusalReason(const RefusalReason &_other)
        : v_(std::move(_other.clone().v_)) {}

    RefusalReason(RefusalReason &&_other) noexcept : v_(std::move(_other.v_)) {}

    RefusalReason &operator=(const RefusalReason &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    RefusalReason &operator=(RefusalReason &&_other) noexcept {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    RefusalReason clone() const {
      if (std::holds_alternative<RefusalInsufficientRank>(this->v())) {
        return RefusalReason(RefusalInsufficientRank{});
      } else {
        const auto &[note] = std::get<RefusalOther>(this->v());
        return RefusalReason(RefusalOther{note});
      }
    }

    // CREATORS
    static RefusalReason refusalinsufficientrank() {
      return RefusalReason(RefusalInsufficientRank{});
    }

    static RefusalReason refusalother(unsigned int note) {
      return RefusalReason(RefusalOther{note});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, unsigned int &>
    T1 RefusalReason_rec(T1 f, F1 &&f0) const {
      if (std::holds_alternative<
              typename RefusalReason::RefusalInsufficientRank>(this->v())) {
        return f;
      } else {
        const auto &[note0] =
            std::get<typename RefusalReason::RefusalOther>(this->v());
        return f0(note0);
      }
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, unsigned int &>
    T1 RefusalReason_rect(T1 f, F1 &&f0) const {
      if (std::holds_alternative<
              typename RefusalReason::RefusalInsufficientRank>(this->v())) {
        return f;
      } else {
        const auto &[note0] =
            std::get<typename RefusalReason::RefusalOther>(this->v());
        return f0(note0);
      }
    }
  };

  struct ProtocolAction {
    // TYPES
    struct ActChallenge {
      BatchallChallenge chal;
    };

    struct ActRespond {
      BatchallResponse resp;
    };

    struct ActRefuse {
      RefusalReason reason;
    };

    struct ActBid {
      ForceBid bid;
    };

    struct ActCoalitionBid {
      CoalitionMemberBid cbid;
    };

    struct ActPass {
      Side side;
    };

    struct ActClose {};

    struct ActWithdraw {
      Side side;
    };

    struct ActBreakBid {
      Side side;
    };

    using variant_t = std::variant<ActChallenge, ActRespond, ActRefuse, ActBid,
                                   ActCoalitionBid, ActPass, ActClose,
                                   ActWithdraw, ActBreakBid>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    ProtocolAction() {}

    explicit ProtocolAction(ActChallenge _v) : v_(std::move(_v)) {}

    explicit ProtocolAction(ActRespond _v) : v_(std::move(_v)) {}

    explicit ProtocolAction(ActRefuse _v) : v_(std::move(_v)) {}

    explicit ProtocolAction(ActBid _v) : v_(std::move(_v)) {}

    explicit ProtocolAction(ActCoalitionBid _v) : v_(std::move(_v)) {}

    explicit ProtocolAction(ActPass _v) : v_(std::move(_v)) {}

    explicit ProtocolAction(ActClose _v) : v_(_v) {}

    explicit ProtocolAction(ActWithdraw _v) : v_(std::move(_v)) {}

    explicit ProtocolAction(ActBreakBid _v) : v_(std::move(_v)) {}

    ProtocolAction(const ProtocolAction &_other)
        : v_(std::move(_other.clone().v_)) {}

    ProtocolAction(ProtocolAction &&_other) noexcept
        : v_(std::move(_other.v_)) {}

    ProtocolAction &operator=(const ProtocolAction &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    ProtocolAction &operator=(ProtocolAction &&_other) noexcept {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    ProtocolAction clone() const {
      if (std::holds_alternative<ActChallenge>(this->v())) {
        const auto &[chal] = std::get<ActChallenge>(this->v());
        return ProtocolAction(ActChallenge{chal.clone()});
      } else if (std::holds_alternative<ActRespond>(this->v())) {
        const auto &[resp] = std::get<ActRespond>(this->v());
        return ProtocolAction(ActRespond{resp.clone()});
      } else if (std::holds_alternative<ActRefuse>(this->v())) {
        const auto &[reason] = std::get<ActRefuse>(this->v());
        return ProtocolAction(ActRefuse{reason.clone()});
      } else if (std::holds_alternative<ActBid>(this->v())) {
        const auto &[bid] = std::get<ActBid>(this->v());
        return ProtocolAction(ActBid{bid.clone()});
      } else if (std::holds_alternative<ActCoalitionBid>(this->v())) {
        const auto &[cbid] = std::get<ActCoalitionBid>(this->v());
        return ProtocolAction(ActCoalitionBid{cbid.clone()});
      } else if (std::holds_alternative<ActPass>(this->v())) {
        const auto &[side] = std::get<ActPass>(this->v());
        return ProtocolAction(ActPass{side});
      } else if (std::holds_alternative<ActClose>(this->v())) {
        return ProtocolAction(ActClose{});
      } else if (std::holds_alternative<ActWithdraw>(this->v())) {
        const auto &[side] = std::get<ActWithdraw>(this->v());
        return ProtocolAction(ActWithdraw{side});
      } else {
        const auto &[side] = std::get<ActBreakBid>(this->v());
        return ProtocolAction(ActBreakBid{side});
      }
    }

    // CREATORS
    static ProtocolAction actchallenge(BatchallChallenge chal) {
      return ProtocolAction(ActChallenge{std::move(chal)});
    }

    static ProtocolAction actrespond(BatchallResponse resp) {
      return ProtocolAction(ActRespond{std::move(resp)});
    }

    static ProtocolAction actrefuse(RefusalReason reason) {
      return ProtocolAction(ActRefuse{std::move(reason)});
    }

    static ProtocolAction actbid(ForceBid bid) {
      return ProtocolAction(ActBid{std::move(bid)});
    }

    static ProtocolAction actcoalitionbid(CoalitionMemberBid cbid) {
      return ProtocolAction(ActCoalitionBid{std::move(cbid)});
    }

    static ProtocolAction actpass(Side side) {
      return ProtocolAction(ActPass{side});
    }

    static ProtocolAction actclose() { return ProtocolAction(ActClose{}); }

    static ProtocolAction actwithdraw(Side side) {
      return ProtocolAction(ActWithdraw{side});
    }

    static ProtocolAction actbreakbid(Side side) {
      return ProtocolAction(ActBreakBid{side});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F0, typename F1, typename F2, typename F3,
            typename F4, typename F5, typename F7, typename F8>
    requires std::is_invocable_r_v<T1, F0 &, BatchallChallenge &> &&
             std::is_invocable_r_v<T1, F1 &, BatchallResponse &> &&
             std::is_invocable_r_v<T1, F2 &, RefusalReason &> &&
             std::is_invocable_r_v<T1, F3 &, ForceBid &> &&
             std::is_invocable_r_v<T1, F4 &, CoalitionMemberBid &> &&
             std::is_invocable_r_v<T1, F5 &, Side &> &&
             std::is_invocable_r_v<T1, F7 &, Side &> &&
             std::is_invocable_r_v<T1, F8 &, Side &>
  static T1 ProtocolAction_rect(F0 &&f, F1 &&f0, F2 &&f1, F3 &&f2, F4 &&f3,
                                F5 &&f4, T1 f5, F7 &&f6, F8 &&f7,
                                const ProtocolAction &p) {
    if (std::holds_alternative<typename ProtocolAction::ActChallenge>(p.v())) {
      const auto &[chal0] =
          std::get<typename ProtocolAction::ActChallenge>(p.v());
      return f(chal0);
    } else if (std::holds_alternative<typename ProtocolAction::ActRespond>(
                   p.v())) {
      const auto &[resp0] =
          std::get<typename ProtocolAction::ActRespond>(p.v());
      return f0(resp0);
    } else if (std::holds_alternative<typename ProtocolAction::ActRefuse>(
                   p.v())) {
      const auto &[reason0] =
          std::get<typename ProtocolAction::ActRefuse>(p.v());
      return f1(reason0);
    } else if (std::holds_alternative<typename ProtocolAction::ActBid>(p.v())) {
      const auto &[bid0] = std::get<typename ProtocolAction::ActBid>(p.v());
      return f2(bid0);
    } else if (std::holds_alternative<typename ProtocolAction::ActCoalitionBid>(
                   p.v())) {
      const auto &[cbid0] =
          std::get<typename ProtocolAction::ActCoalitionBid>(p.v());
      return f3(cbid0);
    } else if (std::holds_alternative<typename ProtocolAction::ActPass>(
                   p.v())) {
      const auto &[side0] = std::get<typename ProtocolAction::ActPass>(p.v());
      return f4(side0);
    } else if (std::holds_alternative<typename ProtocolAction::ActClose>(
                   p.v())) {
      return f5;
    } else if (std::holds_alternative<typename ProtocolAction::ActWithdraw>(
                   p.v())) {
      const auto &[side0] =
          std::get<typename ProtocolAction::ActWithdraw>(p.v());
      return f6(side0);
    } else {
      const auto &[side0] =
          std::get<typename ProtocolAction::ActBreakBid>(p.v());
      return f7(side0);
    }
  }

  template <typename T1, typename F0, typename F1, typename F2, typename F3,
            typename F4, typename F5, typename F7, typename F8>
    requires std::is_invocable_r_v<T1, F0 &, BatchallChallenge &> &&
             std::is_invocable_r_v<T1, F1 &, BatchallResponse &> &&
             std::is_invocable_r_v<T1, F2 &, RefusalReason &> &&
             std::is_invocable_r_v<T1, F3 &, ForceBid &> &&
             std::is_invocable_r_v<T1, F4 &, CoalitionMemberBid &> &&
             std::is_invocable_r_v<T1, F5 &, Side &> &&
             std::is_invocable_r_v<T1, F7 &, Side &> &&
             std::is_invocable_r_v<T1, F8 &, Side &>
  static T1 ProtocolAction_rec(F0 &&f, F1 &&f0, F2 &&f1, F3 &&f2, F4 &&f3,
                               F5 &&f4, T1 f5, F7 &&f6, F8 &&f7,
                               const ProtocolAction &p) {
    if (std::holds_alternative<typename ProtocolAction::ActChallenge>(p.v())) {
      const auto &[chal0] =
          std::get<typename ProtocolAction::ActChallenge>(p.v());
      return f(chal0);
    } else if (std::holds_alternative<typename ProtocolAction::ActRespond>(
                   p.v())) {
      const auto &[resp0] =
          std::get<typename ProtocolAction::ActRespond>(p.v());
      return f0(resp0);
    } else if (std::holds_alternative<typename ProtocolAction::ActRefuse>(
                   p.v())) {
      const auto &[reason0] =
          std::get<typename ProtocolAction::ActRefuse>(p.v());
      return f1(reason0);
    } else if (std::holds_alternative<typename ProtocolAction::ActBid>(p.v())) {
      const auto &[bid0] = std::get<typename ProtocolAction::ActBid>(p.v());
      return f2(bid0);
    } else if (std::holds_alternative<typename ProtocolAction::ActCoalitionBid>(
                   p.v())) {
      const auto &[cbid0] =
          std::get<typename ProtocolAction::ActCoalitionBid>(p.v());
      return f3(cbid0);
    } else if (std::holds_alternative<typename ProtocolAction::ActPass>(
                   p.v())) {
      const auto &[side0] = std::get<typename ProtocolAction::ActPass>(p.v());
      return f4(side0);
    } else if (std::holds_alternative<typename ProtocolAction::ActClose>(
                   p.v())) {
      return f5;
    } else if (std::holds_alternative<typename ProtocolAction::ActWithdraw>(
                   p.v())) {
      const auto &[side0] =
          std::get<typename ProtocolAction::ActWithdraw>(p.v());
      return f6(side0);
    } else {
      const auto &[side0] =
          std::get<typename ProtocolAction::ActBreakBid>(p.v());
      return f7(side0);
    }
  }
  enum class ReadyStatus {
    NEITHERREADY,
    ATTACKERREADY,
    DEFENDERREADY,
    BOTHREADY
  };

  template <typename T1>
  static T1 ReadyStatus_rect(T1 f, T1 f0, T1 f1, T1 f2, ReadyStatus r) {
    switch (r) {
    case ReadyStatus::NEITHERREADY: {
      return f;
    }
    case ReadyStatus::ATTACKERREADY: {
      return f0;
    }
    case ReadyStatus::DEFENDERREADY: {
      return f1;
    }
    case ReadyStatus::BOTHREADY: {
      return f2;
    }
    default:
      std::unreachable();
    }
  }

  template <typename T1>
  static T1 ReadyStatus_rec(T1 f, T1 f0, T1 f1, T1 f2, ReadyStatus r) {
    switch (r) {
    case ReadyStatus::NEITHERREADY: {
      return f;
    }
    case ReadyStatus::ATTACKERREADY: {
      return f0;
    }
    case ReadyStatus::DEFENDERREADY: {
      return f1;
    }
    case ReadyStatus::BOTHREADY: {
      return f2;
    }
    default:
      std::unreachable();
    }
  }

  static bool is_ready(ReadyStatus rs, Side side);
  static ReadyStatus set_ready(ReadyStatus rs, Side side);
  static ReadyStatus clear_ready(ReadyStatus rs, Side side);
  using CoalitionState = std::optional<Coalition>;
  static Force
  coalition_state_force(const std::optional<List<CoalitionMember>> &cs,
                        List<Unit> fallback);

  struct BatchallPhase {
    // TYPES
    struct PhaseIdle {};

    struct PhaseChallenged {
      BatchallChallenge challenge;
    };

    struct PhaseResponded {
      BatchallChallenge challenge;
      BatchallResponse response;
    };

    struct PhaseBidding {
      BatchallChallenge challenge;
      BatchallResponse response;
      ForceBid attacker_bid;
      ForceBid defender_bid;
      CoalitionState attacker_coalition;
      CoalitionState defender_coalition;
      List<ForceBid> bid_history;
      ReadyStatus ready;
    };

    struct PhaseAgreed {
      BatchallChallenge challenge;
      BatchallResponse response;
      ForceBid final_attacker;
      ForceBid final_defender;
    };

    struct PhaseRefused {
      BatchallChallenge challenge;
      RefusalReason reason;
    };

    struct PhaseAborted {
      ProtocolAction reason;
    };

    using variant_t =
        std::variant<PhaseIdle, PhaseChallenged, PhaseResponded, PhaseBidding,
                     PhaseAgreed, PhaseRefused, PhaseAborted>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    BatchallPhase() {}

    explicit BatchallPhase(PhaseIdle _v) : v_(_v) {}

    explicit BatchallPhase(PhaseChallenged _v) : v_(std::move(_v)) {}

    explicit BatchallPhase(PhaseResponded _v) : v_(std::move(_v)) {}

    explicit BatchallPhase(PhaseBidding _v) : v_(std::move(_v)) {}

    explicit BatchallPhase(PhaseAgreed _v) : v_(std::move(_v)) {}

    explicit BatchallPhase(PhaseRefused _v) : v_(std::move(_v)) {}

    explicit BatchallPhase(PhaseAborted _v) : v_(std::move(_v)) {}

    BatchallPhase(const BatchallPhase &_other)
        : v_(std::move(_other.clone().v_)) {}

    BatchallPhase(BatchallPhase &&_other) noexcept : v_(std::move(_other.v_)) {}

    BatchallPhase &operator=(const BatchallPhase &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    BatchallPhase &operator=(BatchallPhase &&_other) noexcept {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    BatchallPhase clone() const {
      if (std::holds_alternative<PhaseIdle>(this->v())) {
        return BatchallPhase(PhaseIdle{});
      } else if (std::holds_alternative<PhaseChallenged>(this->v())) {
        const auto &[challenge] = std::get<PhaseChallenged>(this->v());
        return BatchallPhase(PhaseChallenged{challenge.clone()});
      } else if (std::holds_alternative<PhaseResponded>(this->v())) {
        const auto &[challenge, response] = std::get<PhaseResponded>(this->v());
        return BatchallPhase(
            PhaseResponded{challenge.clone(), response.clone()});
      } else if (std::holds_alternative<PhaseBidding>(this->v())) {
        const auto &[challenge, response, attacker_bid, defender_bid,
                     attacker_coalition, defender_coalition, bid_history,
                     ready] = std::get<PhaseBidding>(this->v());
        return BatchallPhase(PhaseBidding{
            challenge.clone(), response.clone(), attacker_bid.clone(),
            defender_bid.clone(), attacker_coalition, defender_coalition,
            bid_history.clone(), ready});
      } else if (std::holds_alternative<PhaseAgreed>(this->v())) {
        const auto &[challenge, response, final_attacker, final_defender] =
            std::get<PhaseAgreed>(this->v());
        return BatchallPhase(PhaseAgreed{challenge.clone(), response.clone(),
                                         final_attacker.clone(),
                                         final_defender.clone()});
      } else if (std::holds_alternative<PhaseRefused>(this->v())) {
        const auto &[challenge, reason] = std::get<PhaseRefused>(this->v());
        return BatchallPhase(PhaseRefused{challenge.clone(), reason.clone()});
      } else {
        const auto &[reason] = std::get<PhaseAborted>(this->v());
        return BatchallPhase(PhaseAborted{reason.clone()});
      }
    }

    // CREATORS
    static BatchallPhase phaseidle() { return BatchallPhase(PhaseIdle{}); }

    static BatchallPhase phasechallenged(BatchallChallenge challenge) {
      return BatchallPhase(PhaseChallenged{std::move(challenge)});
    }

    static BatchallPhase phaseresponded(BatchallChallenge challenge,
                                        BatchallResponse response) {
      return BatchallPhase(
          PhaseResponded{std::move(challenge), std::move(response)});
    }

    static BatchallPhase
    phasebidding(BatchallChallenge challenge, BatchallResponse response,
                 ForceBid attacker_bid, ForceBid defender_bid,
                 CoalitionState attacker_coalition,
                 CoalitionState defender_coalition, List<ForceBid> bid_history,
                 ReadyStatus ready) {
      return BatchallPhase(PhaseBidding{
          std::move(challenge), std::move(response), std::move(attacker_bid),
          std::move(defender_bid), std::move(attacker_coalition),
          std::move(defender_coalition), std::move(bid_history), ready});
    }

    static BatchallPhase phaseagreed(BatchallChallenge challenge,
                                     BatchallResponse response,
                                     ForceBid final_attacker,
                                     ForceBid final_defender) {
      return BatchallPhase(
          PhaseAgreed{std::move(challenge), std::move(response),
                      std::move(final_attacker), std::move(final_defender)});
    }

    static BatchallPhase phaserefused(BatchallChallenge challenge,
                                      RefusalReason reason) {
      return BatchallPhase(
          PhaseRefused{std::move(challenge), std::move(reason)});
    }

    static BatchallPhase phaseaborted(ProtocolAction reason) {
      return BatchallPhase(PhaseAborted{std::move(reason)});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    std::optional<Commander>
    action_actor_in_phase(const ProtocolAction &action) const {
      if (std::holds_alternative<typename ProtocolAction::ActChallenge>(
              action.v())) {
        const auto &[chal0] =
            std::get<typename ProtocolAction::ActChallenge>(action.v());
        return std::make_optional<Commander>(chal0.chal_challenger);
      } else if (std::holds_alternative<typename ProtocolAction::ActRespond>(
                     action.v())) {
        const auto &[resp0] =
            std::get<typename ProtocolAction::ActRespond>(action.v());
        return std::make_optional<Commander>(resp0.resp_defender);
      } else if (std::holds_alternative<typename ProtocolAction::ActBid>(
                     action.v())) {
        const auto &[bid0] =
            std::get<typename ProtocolAction::ActBid>(action.v());
        return std::make_optional<Commander>(bid0.bid_commander);
      } else if (std::holds_alternative<typename ProtocolAction::ActWithdraw>(
                     action.v())) {
        const auto &[side0] =
            std::get<typename ProtocolAction::ActWithdraw>(action.v());
        return (*this).get_side_commander(side0);
      } else if (std::holds_alternative<typename ProtocolAction::ActBreakBid>(
                     action.v())) {
        const auto &[side0] =
            std::get<typename ProtocolAction::ActBreakBid>(action.v());
        return (*this).get_side_commander(side0);
      } else {
        return std::optional<Commander>();
      }
    }

    std::optional<Commander> get_side_commander(Side side) const {
      if (std::holds_alternative<typename BatchallPhase::PhaseBidding>(
              this->v())) {
        const auto &[challenge, response, attacker_bid, defender_bid,
                     attacker_coalition0, defender_coalition0, bid_history,
                     ready] =
            std::get<typename BatchallPhase::PhaseBidding>(this->v());
        switch (side) {
        case Side::ATTACKER: {
          return std::make_optional<Commander>(attacker_bid.bid_commander);
        }
        case Side::DEFENDER: {
          return std::make_optional<Commander>(defender_bid.bid_commander);
        }
        default:
          std::unreachable();
        }
      } else {
        return std::optional<Commander>();
      }
    }

    unsigned int get_bidding_measure() const {
      if (std::holds_alternative<typename BatchallPhase::PhaseBidding>(
              this->v())) {
        const auto &[challenge, response, attacker_bid, defender_bid,
                     attacker_coalition0, defender_coalition0, bid_history,
                     ready0] =
            std::get<typename BatchallPhase::PhaseBidding>(this->v());
        return ((bid_metrics(attacker_bid).fm_total_ecr +
                 bid_metrics(defender_bid).fm_total_ecr) +
                [&]() {
                  switch (ready0) {
                  case ReadyStatus::NEITHERREADY: {
                    return 2u;
                  }
                  case ReadyStatus::BOTHREADY: {
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

    unsigned int phase_depth() const {
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

    bool is_bidding() const {
      if (std::holds_alternative<typename BatchallPhase::PhaseBidding>(
              this->v())) {
        return true;
      } else {
        return false;
      }
    }

    bool is_terminal() const {
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

  template <typename T1, typename F1, typename F2, typename F3, typename F4,
            typename F5, typename F6>
    requires std::is_invocable_r_v<T1, F1 &, BatchallChallenge &> &&
             std::is_invocable_r_v<T1, F2 &, BatchallChallenge &,
                                   BatchallResponse &> &&
             std::is_invocable_r_v<T1, F3 &, BatchallChallenge &,
                                   BatchallResponse &, ForceBid &, ForceBid &,
                                   std::optional<List<CoalitionMember>> &,
                                   std::optional<List<CoalitionMember>> &,
                                   List<ForceBid> &, ReadyStatus &> &&
             std::is_invocable_r_v<T1, F4 &, BatchallChallenge &,
                                   BatchallResponse &, ForceBid &,
                                   ForceBid &> &&
             std::is_invocable_r_v<T1, F5 &, BatchallChallenge &,
                                   RefusalReason &> &&
             std::is_invocable_r_v<T1, F6 &, ProtocolAction &>
  static T1 BatchallPhase_rect(T1 f, F1 &&f0, F2 &&f1, F3 &&f2, F4 &&f3,
                               F5 &&f4, F6 &&f5, const BatchallPhase &b) {
    if (std::holds_alternative<typename BatchallPhase::PhaseIdle>(b.v())) {
      return f;
    } else if (std::holds_alternative<typename BatchallPhase::PhaseChallenged>(
                   b.v())) {
      const auto &[challenge0] =
          std::get<typename BatchallPhase::PhaseChallenged>(b.v());
      return f0(challenge0);
    } else if (std::holds_alternative<typename BatchallPhase::PhaseResponded>(
                   b.v())) {
      const auto &[challenge0, response0] =
          std::get<typename BatchallPhase::PhaseResponded>(b.v());
      return f1(challenge0, response0);
    } else if (std::holds_alternative<typename BatchallPhase::PhaseBidding>(
                   b.v())) {
      const auto &[challenge0, response0, attacker_bid0, defender_bid0,
                   attacker_coalition1, defender_coalition1, bid_history0,
                   ready0] =
          std::get<typename BatchallPhase::PhaseBidding>(b.v());
      return f2(challenge0, response0, attacker_bid0, defender_bid0,
                attacker_coalition1, defender_coalition1, bid_history0, ready0);
    } else if (std::holds_alternative<typename BatchallPhase::PhaseAgreed>(
                   b.v())) {
      const auto &[challenge0, response0, final_attacker0, final_defender0] =
          std::get<typename BatchallPhase::PhaseAgreed>(b.v());
      return f3(challenge0, response0, final_attacker0, final_defender0);
    } else if (std::holds_alternative<typename BatchallPhase::PhaseRefused>(
                   b.v())) {
      const auto &[challenge0, reason0] =
          std::get<typename BatchallPhase::PhaseRefused>(b.v());
      return f4(challenge0, reason0);
    } else {
      const auto &[reason0] =
          std::get<typename BatchallPhase::PhaseAborted>(b.v());
      return f5(reason0);
    }
  }

  template <typename T1, typename F1, typename F2, typename F3, typename F4,
            typename F5, typename F6>
    requires std::is_invocable_r_v<T1, F1 &, BatchallChallenge &> &&
             std::is_invocable_r_v<T1, F2 &, BatchallChallenge &,
                                   BatchallResponse &> &&
             std::is_invocable_r_v<T1, F3 &, BatchallChallenge &,
                                   BatchallResponse &, ForceBid &, ForceBid &,
                                   std::optional<List<CoalitionMember>> &,
                                   std::optional<List<CoalitionMember>> &,
                                   List<ForceBid> &, ReadyStatus &> &&
             std::is_invocable_r_v<T1, F4 &, BatchallChallenge &,
                                   BatchallResponse &, ForceBid &,
                                   ForceBid &> &&
             std::is_invocable_r_v<T1, F5 &, BatchallChallenge &,
                                   RefusalReason &> &&
             std::is_invocable_r_v<T1, F6 &, ProtocolAction &>
  static T1 BatchallPhase_rec(T1 f, F1 &&f0, F2 &&f1, F3 &&f2, F4 &&f3, F5 &&f4,
                              F6 &&f5, const BatchallPhase &b) {
    if (std::holds_alternative<typename BatchallPhase::PhaseIdle>(b.v())) {
      return f;
    } else if (std::holds_alternative<typename BatchallPhase::PhaseChallenged>(
                   b.v())) {
      const auto &[challenge0] =
          std::get<typename BatchallPhase::PhaseChallenged>(b.v());
      return f0(challenge0);
    } else if (std::holds_alternative<typename BatchallPhase::PhaseResponded>(
                   b.v())) {
      const auto &[challenge0, response0] =
          std::get<typename BatchallPhase::PhaseResponded>(b.v());
      return f1(challenge0, response0);
    } else if (std::holds_alternative<typename BatchallPhase::PhaseBidding>(
                   b.v())) {
      const auto &[challenge0, response0, attacker_bid0, defender_bid0,
                   attacker_coalition1, defender_coalition1, bid_history0,
                   ready0] =
          std::get<typename BatchallPhase::PhaseBidding>(b.v());
      return f2(challenge0, response0, attacker_bid0, defender_bid0,
                attacker_coalition1, defender_coalition1, bid_history0, ready0);
    } else if (std::holds_alternative<typename BatchallPhase::PhaseAgreed>(
                   b.v())) {
      const auto &[challenge0, response0, final_attacker0, final_defender0] =
          std::get<typename BatchallPhase::PhaseAgreed>(b.v());
      return f3(challenge0, response0, final_attacker0, final_defender0);
    } else if (std::holds_alternative<typename BatchallPhase::PhaseRefused>(
                   b.v())) {
      const auto &[challenge0, reason0] =
          std::get<typename BatchallPhase::PhaseRefused>(b.v());
      return f4(challenge0, reason0);
    } else {
      const auto &[reason0] =
          std::get<typename BatchallPhase::PhaseAborted>(b.v());
      return f5(reason0);
    }
  }

  using Honor = Z;
  using HonorEntry = std::pair<unsigned int, Honor>;
  using HonorLedger = List<HonorEntry>;
  static Honor ledger_lookup(const List<std::pair<unsigned int, Z>> &ledger,
                             unsigned int warrior_id);
  static HonorLedger
  ledger_update_by_id(const List<std::pair<unsigned int, Z>> &ledger,
                      unsigned int warrior_id, Z new_honor);
  static HonorLedger
  update_honor(const List<std::pair<unsigned int, Z>> &ledger,
               const Commander &actor, const Z &delta);
  static Honor refusal_honor_delta(const RefusalReason &r);
  static Honor protocol_honor_delta(const ProtocolAction &action);

  struct BatchallState {
    BatchallPhase bs_phase;
    HonorLedger bs_honor;

    // ACCESSORS
    BatchallState clone() const {
      return BatchallState{(*this).bs_phase.clone(), (*this).bs_honor};
    }
  };

  static inline const HonorLedger empty_ledger =
      List<std::pair<unsigned int, Z>>::nil();
  static inline const BatchallState initial_state =
      BatchallState{BatchallPhase::phaseidle(), empty_ledger};
  static HonorLedger apply_action_honor(const BatchallState &state,
                                        const ProtocolAction &action);
  static inline const Commander malthus =
      Commander{1u, Clan::CLANJADEFALCON, Rank::STARCOLONEL, true};
  static inline const Commander radick =
      Commander{2u, Clan::CLANWOLF, Rank::STARCAPTAIN, true};
  static inline const Commander bear_ally =
      Commander{3u, Clan::CLANGHOSTBEAR, Rank::STARCAPTAIN, false};
  static inline const Unit timberwolf = Unit{
      101u, UnitClass::OMNIMECH, WeightClass::HEAVY, 75u, 2u, 3u, true, true};
  static inline const Unit direwolf =
      Unit{102u, UnitClass::OMNIMECH, WeightClass::ASSAULT, 100u, 2u, 3u, true,
           true};
  static inline const Unit summoner = Unit{
      103u, UnitClass::OMNIMECH, WeightClass::HEAVY, 70u, 3u, 4u, false, true};
  static inline const Unit mad_dog = Unit{
      104u, UnitClass::OMNIMECH, WeightClass::HEAVY, 60u, 3u, 4u, false, true};
  static inline const Unit elementals = Unit{
      105u, UnitClass::ELEMENTAL, WeightClass::LIGHT, 5u, 3u, 4u, false, true};
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
          CoalitionMember{Clan::CLANJADEFALCON, malthus, falcon_trinary},
          List<CoalitionMember>::cons(
              CoalitionMember{Clan::CLANGHOSTBEAR, bear_ally, bear_support},
              List<CoalitionMember>::nil()));
  static inline const Coalition defender_coalition =
      List<CoalitionMember>::cons(
          CoalitionMember{Clan::CLANWOLF, radick, wolf_binary},
          List<CoalitionMember>::nil());
  static inline const BatchallChallenge sample_challenge =
      BatchallChallenge{malthus,
                        Clan::CLANJADEFALCON,
                        Prize::prizeenclave(42u),
                        coalition_force(attacker_coalition),
                        Location::locplanetsurface(7u, 3u),
                        TrialType::TRIALOFPOSSESSION,
                        standard_possession_context};
  static inline const BatchallResponse sample_response = BatchallResponse{
      radick, Clan::CLANWOLF, coalition_force(defender_coalition)};
  static inline const ForceBid sample_attacker_bid = []() -> ForceBid {
    auto _cs = coalition_to_bid(attacker_coalition, Side::ATTACKER);
    if (_cs.has_value()) {
      const ForceBid &bid = *_cs;
      return bid;
    } else {
      return ForceBid{List<Unit>::nil(), Side::ATTACKER, malthus};
    }
  }();
  static inline const ForceBid sample_defender_bid = []() -> ForceBid {
    auto _cs = coalition_to_bid(defender_coalition, Side::DEFENDER);
    if (_cs.has_value()) {
      const ForceBid &bid = *_cs;
      return bid;
    } else {
      return ForceBid{List<Unit>::nil(), Side::DEFENDER, radick};
    }
  }();
  static inline const Force reduced_support_force =
      List<Unit>::cons(elementals, List<Unit>::nil());
  static inline const CoalitionMemberBid sample_coalition_member_bid =
      CoalitionMemberBid{1u, reduced_support_force, Side::ATTACKER};
  static inline const Coalition updated_attacker_coalition =
      apply_coalition_member_bid(attacker_coalition,
                                 sample_coalition_member_bid);
  static inline const ForceBid updated_attacker_bid = []() -> ForceBid {
    auto _cs = coalition_to_bid(updated_attacker_coalition, Side::ATTACKER);
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
          List<ForceBid>::nil(), ReadyStatus::NEITHERREADY);
  static inline const BatchallPhase phase_after_attacker_pass =
      BatchallPhase::phasebidding(
          sample_challenge, sample_response, sample_attacker_bid,
          sample_defender_bid,
          std::make_optional<List<CoalitionMember>>(attacker_coalition),
          std::make_optional<List<CoalitionMember>>(defender_coalition),
          List<ForceBid>::nil(), ReadyStatus::ATTACKERREADY);
  static inline const BatchallPhase phase_after_coalition_bid =
      BatchallPhase::phasebidding(
          sample_challenge, sample_response, updated_attacker_bid,
          sample_defender_bid,
          std::make_optional<List<CoalitionMember>>(updated_attacker_coalition),
          std::make_optional<List<CoalitionMember>>(defender_coalition),
          List<ForceBid>::cons(sample_attacker_bid, List<ForceBid>::nil()),
          ReadyStatus::NEITHERREADY);
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
                         ProtocolAction::actbreakbid(Side::ATTACKER));
  static inline const bool sample_challenger_may_issue =
      may_issue_batchall(malthus);
  static inline const bool sample_coalition_bid_is_valid =
      valid_coalition_member_bid_b(attacker_coalition,
                                   sample_coalition_member_bid);
  static inline const bool sample_coalition_contains_bear =
      coalition_contains_clan(attacker_coalition, Clan::CLANGHOSTBEAR);
  static inline const bool sample_updated_tonnage_reduced =
      coalition_tonnage(updated_attacker_coalition) <
      coalition_tonnage(attacker_coalition);
  static inline const bool sample_attacker_ready_after_pass = is_ready(
      set_ready(ReadyStatus::NEITHERREADY, Side::ATTACKER), Side::ATTACKER);
  static inline const bool sample_attacker_not_ready_after_clear = !(is_ready(
      clear_ready(ReadyStatus::BOTHREADY, Side::ATTACKER), Side::ATTACKER));
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
        ProtocolAction::actbreakbid(Side::ATTACKER));
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
T1 ListDef::nth(unsigned int n, const List<T1> &l, T1 default0) {
  if (n <= 0) {
    if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
      return default0;
    } else {
      const auto &[a0, a1] = std::get<typename List<T1>::Cons>(l.v());
      return a0;
    }
  } else {
    unsigned int m = n - 1;
    if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
      return default0;
    } else {
      const auto &[a00, a10] = std::get<typename List<T1>::Cons>(l.v());
      return ListDef::template nth<T1>(m, *a10, default0);
    }
  }
}

#endif // INCLUDED_COALITION_BID_HONOR_TRACE
