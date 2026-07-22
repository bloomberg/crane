#ifndef INCLUDED_VALIDATED_VIRTUAL_CROSSMATCH_TRACE
#define INCLUDED_VALIDATED_VIRTUAL_CROSSMATCH_TRACE

#include <algorithm>
#include <any>
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

  template <typename _U> explicit List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      this->v_ = Nil{};
    } else {
      const auto &[a, l] = std::get<typename List<_U>::Cons>(_other.v());
      this->v_ = Cons{
          [&]() -> A {
            if constexpr (std::is_same_v<_U, std::any>) {
              if (a.type() == typeid(A))
                return std::any_cast<A>(a);
              if constexpr (requires {
                              typename A::first_type;
                              typename A::second_type;
                            }) {
                const auto &[_k, _v] =
                    std::any_cast<std::pair<std::any, std::any>>(a);
                return A{[&]() -> typename A::first_type {
                           if constexpr (std::is_same_v<typename A::first_type,
                                                        std::any>)
                             return _k;
                           else
                             return std::any_cast<typename A::first_type>(_k);
                         }(),
                         [&]() -> typename A::second_type {
                           if constexpr (std::is_same_v<typename A::second_type,
                                                        std::any>)
                             return _v;
                           else
                             return std::any_cast<typename A::second_type>(_v);
                         }()};
              }
              return std::any_cast<A>(a);
            } else
              return A(a);
          }(),
          l ? std::make_shared<List<A>>(*l) : nullptr};
    }
  }

  static List<A> nil() { return List(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List(Cons{std::move(a), std::make_shared<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  ~List() {
    std::vector<std::shared_ptr<List<A>>> _stack = {};
    auto _drain = [&](variant_t &_v) {
      if (auto *_alt = std::get_if<Cons>(&_v)) {
        if (_alt->l) {
          _stack.push_back(std::move(_alt->l));
        }
      }
    };
    _drain(v_mut());
    while (!_stack.empty()) {
      auto _cur = std::move(_stack.back());
      _stack.pop_back();
      if (_cur.use_count() == 1) {
        _drain(_cur->v_mut());
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
      return (f(a0) || a1->existsb(f));
    }
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, T1 &, A &>
  T1 fold_left(F0 &&f, T1 a0) const {
    if (std::holds_alternative<typename List<A>::Nil>(this->v())) {
      return a0;
    } else {
      const auto &[a1, a2] = std::get<typename List<A>::Cons>(this->v());
      return a2->template fold_left<T1>(f, f(a0, a1));
    }
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<List<T1>, F0 &, A &>
  List<T1> flat_map(F0 &&f) const {
    if (std::holds_alternative<typename List<A>::Nil>(this->v())) {
      return List<T1>::nil();
    } else {
      const auto &[a0, a1] = std::get<typename List<A>::Cons>(this->v());
      return f(a0).app(a1->template flat_map<T1>(f));
    }
  }

  uint64_t length() const {
    if (std::holds_alternative<typename List<A>::Nil>(this->v())) {
      return UINT64_C(0);
    } else {
      const auto &[a0, a1] = std::get<typename List<A>::Cons>(this->v());
      return (a1->length() + 1);
    }
  }

  List<A> app(List<A> m) const {
    if (std::holds_alternative<typename List<A>::Nil>(this->v())) {
      return m;
    } else {
      const auto &[a0, a1] = std::get<typename List<A>::Cons>(this->v());
      return List<A>::cons(a0, a1->app(std::move(m)));
    }
  }
};

struct PeanoNat {
  static bool eq_dec(uint64_t n, uint64_t m);
};

struct Bool {
  static bool bool_dec(bool b1, bool b2);
};

struct ValidatedVirtualCrossmatchTraceCase {
  enum class HLALocus { LOCUS_A, LOCUS_B, LOCUS_DR };

  template <typename T1>
  static T1 HLALocus_rect(T1 f, T1 f0, T1 f1, HLALocus h) {
    switch (h) {
    case HLALocus::LOCUS_A: {
      return f;
    }
    case HLALocus::LOCUS_B: {
      return f0;
    }
    case HLALocus::LOCUS_DR: {
      return f1;
    }
    default:
      std::unreachable();
    }
  }

  template <typename T1>
  static T1 HLALocus_rec(T1 f, T1 f0, T1 f1, HLALocus h) {
    switch (h) {
    case HLALocus::LOCUS_A: {
      return f;
    }
    case HLALocus::LOCUS_B: {
      return f0;
    }
    case HLALocus::LOCUS_DR: {
      return f1;
    }
    default:
      std::unreachable();
    }
  }

  static bool hla_locus_eq_dec(HLALocus x, HLALocus y);

  struct HLAAllele {
    HLALocus hla_locus;
    uint64_t hla_group;
  };

  static bool hla_allele_eq_dec(const HLAAllele &x, const HLAAllele &y);
  static bool hla_allele_eqb(const HLAAllele &x, const HLAAllele &y);

  struct HLATyping {
    List<HLAAllele> hla_typed_alleles;
  };

  struct HLAEpitope {
    uint64_t epitope_id;
    HLALocus epitope_locus;
    bool epitope_immunogenic;
  };

  static bool epitope_eq_dec(const HLAEpitope &x, const HLAEpitope &y);
  static bool epitope_eqb(const HLAEpitope &x, const HLAEpitope &y);
  static inline const HLAEpitope eplet_62GE =
      HLAEpitope{UINT64_C(62), HLALocus::LOCUS_A, true};
  static inline const HLAEpitope eplet_65QIA =
      HLAEpitope{UINT64_C(65), HLALocus::LOCUS_A, true};
  static inline const HLAEpitope eplet_142T =
      HLAEpitope{UINT64_C(142), HLALocus::LOCUS_B, true};
  static inline const HLAEpitope eplet_77N =
      HLAEpitope{UINT64_C(77), HLALocus::LOCUS_DR, true};
  static List<HLAEpitope> allele_epitopes(const HLAAllele &a);
  static List<HLAEpitope> typing_epitopes(const HLATyping &t);
  static List<HLAEpitope> epitope_dedup(const List<HLAEpitope> &l);

  struct EpitopeAntibody {
    HLAEpitope ab_epitope;
    uint64_t ab_mfi;
    bool ab_complement_fixing;
  };

  struct VirtualXMProfile {
    List<EpitopeAntibody> vxm_epitope_abs;
    uint64_t vxm_current_pra;
    uint64_t vxm_peak_pra;
    uint64_t vxm_sensitization_events;
  };

  struct MFIThresholdConfig {
    uint64_t mfi_cfg_negative;
    uint64_t mfi_cfg_weak_positive;
    uint64_t mfi_cfg_moderate;
    uint64_t mfi_cfg_strong;
    uint64_t mfi_cfg_lab_id;
    bool mfi_cfg_validated;
  };

  static bool mfi_config_valid(const MFIThresholdConfig &cfg);
  static inline const MFIThresholdConfig example_luminex_thresholds =
      MFIThresholdConfig{UINT64_C(1000),  UINT64_C(3000), UINT64_C(8000),
                         UINT64_C(12000), UINT64_C(1),    true};

  struct ValidatedMFIConfig {
    MFIThresholdConfig vmc_config;
  };

  static inline const ValidatedMFIConfig validated_luminex =
      ValidatedMFIConfig{example_luminex_thresholds};
  enum class MFIStrength {
    MFI_NEGATIVE,
    MFI_WEAKPOSITIVE,
    MFI_MODERATE,
    MFI_STRONG,
    MFI_VERYSTRONG
  };

  template <typename T1>
  static T1 MFIStrength_rect(T1 f, T1 f0, T1 f1, T1 f2, T1 f3, MFIStrength m) {
    switch (m) {
    case MFIStrength::MFI_NEGATIVE: {
      return f;
    }
    case MFIStrength::MFI_WEAKPOSITIVE: {
      return f0;
    }
    case MFIStrength::MFI_MODERATE: {
      return f1;
    }
    case MFIStrength::MFI_STRONG: {
      return f2;
    }
    case MFIStrength::MFI_VERYSTRONG: {
      return f3;
    }
    default:
      std::unreachable();
    }
  }

  template <typename T1>
  static T1 MFIStrength_rec(T1 f, T1 f0, T1 f1, T1 f2, T1 f3, MFIStrength m) {
    switch (m) {
    case MFIStrength::MFI_NEGATIVE: {
      return f;
    }
    case MFIStrength::MFI_WEAKPOSITIVE: {
      return f0;
    }
    case MFIStrength::MFI_MODERATE: {
      return f1;
    }
    case MFIStrength::MFI_STRONG: {
      return f2;
    }
    case MFIStrength::MFI_VERYSTRONG: {
      return f3;
    }
    default:
      std::unreachable();
    }
  }

  static MFIStrength classify_mfi_with_config(const MFIThresholdConfig &cfg,
                                              uint64_t mfi);
  static MFIStrength classify_mfi_safe(const ValidatedMFIConfig &vcfg,
                                       uint64_t mfi);
  static inline const uint64_t mfi_negative_threshold = UINT64_C(1000);
  static uint64_t max_dsa_mfi(const VirtualXMProfile &recipient,
                              const HLATyping &donor);
  static bool has_complement_fixing_dsa(const VirtualXMProfile &recipient,
                                        const HLATyping &donor);
  enum class VirtualXMResult {
    VXM_NEGATIVE,
    VXM_WEAKPOSITIVE,
    VXM_POSITIVE,
    VXM_STRONGPOSITIVE
  };

  template <typename T1>
  static T1 VirtualXMResult_rect(T1 f, T1 f0, T1 f1, T1 f2, VirtualXMResult v) {
    switch (v) {
    case VirtualXMResult::VXM_NEGATIVE: {
      return f;
    }
    case VirtualXMResult::VXM_WEAKPOSITIVE: {
      return f0;
    }
    case VirtualXMResult::VXM_POSITIVE: {
      return f1;
    }
    case VirtualXMResult::VXM_STRONGPOSITIVE: {
      return f2;
    }
    default:
      std::unreachable();
    }
  }

  template <typename T1>
  static T1 VirtualXMResult_rec(T1 f, T1 f0, T1 f1, T1 f2, VirtualXMResult v) {
    switch (v) {
    case VirtualXMResult::VXM_NEGATIVE: {
      return f;
    }
    case VirtualXMResult::VXM_WEAKPOSITIVE: {
      return f0;
    }
    case VirtualXMResult::VXM_POSITIVE: {
      return f1;
    }
    case VirtualXMResult::VXM_STRONGPOSITIVE: {
      return f2;
    }
    default:
      std::unreachable();
    }
  }

  static VirtualXMResult
  virtual_crossmatch_safe(const ValidatedMFIConfig &vcfg,
                          const VirtualXMProfile &recipient,
                          const HLATyping &donor);
  enum class TransplantAcceptability {
    ACCEPTABLE,
    ACCEPTABLE_WITH_DESENSITIZATION,
    UNACCEPTABLE_HIGH_RISK,
    ABSOLUTE_CONTRAINDICATION
  };

  template <typename T1>
  static T1 TransplantAcceptability_rect(T1 f, T1 f0, T1 f1, T1 f2,
                                         TransplantAcceptability t) {
    switch (t) {
    case TransplantAcceptability::ACCEPTABLE: {
      return f;
    }
    case TransplantAcceptability::ACCEPTABLE_WITH_DESENSITIZATION: {
      return f0;
    }
    case TransplantAcceptability::UNACCEPTABLE_HIGH_RISK: {
      return f1;
    }
    case TransplantAcceptability::ABSOLUTE_CONTRAINDICATION: {
      return f2;
    }
    default:
      std::unreachable();
    }
  }

  template <typename T1>
  static T1 TransplantAcceptability_rec(T1 f, T1 f0, T1 f1, T1 f2,
                                        TransplantAcceptability t) {
    switch (t) {
    case TransplantAcceptability::ACCEPTABLE: {
      return f;
    }
    case TransplantAcceptability::ACCEPTABLE_WITH_DESENSITIZATION: {
      return f0;
    }
    case TransplantAcceptability::UNACCEPTABLE_HIGH_RISK: {
      return f1;
    }
    case TransplantAcceptability::ABSOLUTE_CONTRAINDICATION: {
      return f2;
    }
    default:
      std::unreachable();
    }
  }

  static TransplantAcceptability
  transplant_acceptability(VirtualXMResult vxm, bool complement_fixing_dsa);
  static TransplantAcceptability
  full_virtual_crossmatch_safe(const ValidatedMFIConfig &vcfg,
                               const VirtualXMProfile &recipient,
                               const HLATyping &donor);
  enum class TestConfidence {
    CONFIDENCE_HIGH,
    CONFIDENCE_MEDIUM,
    CONFIDENCE_LOW
  };

  template <typename T1>
  static T1 TestConfidence_rect(T1 f, T1 f0, T1 f1, TestConfidence t) {
    switch (t) {
    case TestConfidence::CONFIDENCE_HIGH: {
      return f;
    }
    case TestConfidence::CONFIDENCE_MEDIUM: {
      return f0;
    }
    case TestConfidence::CONFIDENCE_LOW: {
      return f1;
    }
    default:
      std::unreachable();
    }
  }

  template <typename T1>
  static T1 TestConfidence_rec(T1 f, T1 f0, T1 f1, TestConfidence t) {
    switch (t) {
    case TestConfidence::CONFIDENCE_HIGH: {
      return f;
    }
    case TestConfidence::CONFIDENCE_MEDIUM: {
      return f0;
    }
    case TestConfidence::CONFIDENCE_LOW: {
      return f1;
    }
    default:
      std::unreachable();
    }
  }
  enum class CrossmatchResult {
    XM_COMPATIBLE,
    XM_INCOMPATIBLE,
    XM_INCONCLUSIVE,
    XM_NOT_DONE
  };

  template <typename T1>
  static T1 CrossmatchResult_rect(T1 f, T1 f0, T1 f1, T1 f2,
                                  CrossmatchResult c) {
    switch (c) {
    case CrossmatchResult::XM_COMPATIBLE: {
      return f;
    }
    case CrossmatchResult::XM_INCOMPATIBLE: {
      return f0;
    }
    case CrossmatchResult::XM_INCONCLUSIVE: {
      return f1;
    }
    case CrossmatchResult::XM_NOT_DONE: {
      return f2;
    }
    default:
      std::unreachable();
    }
  }

  template <typename T1>
  static T1 CrossmatchResult_rec(T1 f, T1 f0, T1 f1, T1 f2,
                                 CrossmatchResult c) {
    switch (c) {
    case CrossmatchResult::XM_COMPATIBLE: {
      return f;
    }
    case CrossmatchResult::XM_INCOMPATIBLE: {
      return f0;
    }
    case CrossmatchResult::XM_INCONCLUSIVE: {
      return f1;
    }
    case CrossmatchResult::XM_NOT_DONE: {
      return f2;
    }
    default:
      std::unreachable();
    }
  }

  struct CrossmatchWithUncertainty {
    CrossmatchResult xmu_result;
    uint64_t xmu_method;
    TestConfidence xmu_confidence;
  };

  static bool safe_to_release(const CrossmatchWithUncertainty &xm);

  struct SafeTransfusionOrder {
    uint64_t sto_recipient_id;
    uint64_t sto_product_id;
    bool sto_compatibility_check;
    CrossmatchWithUncertainty sto_crossmatch;
    uint64_t sto_sample_collection_time;
    uint64_t sto_authorized_by;
    bool sto_emergency_release;
  };

  static bool order_sample_valid(uint64_t collection_time,
                                 uint64_t current_time);
  static bool transfusion_order_authorized(const SafeTransfusionOrder &order,
                                           uint64_t current_time);
  static std::optional<SafeTransfusionOrder> create_safe_transfusion_order(
      uint64_t recipient_id, uint64_t product_id, bool compat_result,
      CrossmatchWithUncertainty xm, uint64_t sample_time, uint64_t current_time,
      uint64_t authorizer, bool is_emergency);
  static inline const HLATyping donor_hla = HLATyping{List<HLAAllele>::cons(
      HLAAllele{HLALocus::LOCUS_A, UINT64_C(2)},
      List<HLAAllele>::cons(
          HLAAllele{HLALocus::LOCUS_A, UINT64_C(3)},
          List<HLAAllele>::cons(
              HLAAllele{HLALocus::LOCUS_B, UINT64_C(7)},
              List<HLAAllele>::cons(HLAAllele{HLALocus::LOCUS_DR, UINT64_C(4)},
                                    List<HLAAllele>::nil()))))};
  static inline const VirtualXMProfile weak_profile =
      VirtualXMProfile{List<EpitopeAntibody>::cons(
                           EpitopeAntibody{eplet_65QIA, UINT64_C(2500), false},
                           List<EpitopeAntibody>::cons(
                               EpitopeAntibody{eplet_77N, UINT64_C(800), false},
                               List<EpitopeAntibody>::nil())),
                       UINT64_C(32), UINT64_C(40), UINT64_C(2)};
  static inline const VirtualXMProfile strong_profile = VirtualXMProfile{
      List<EpitopeAntibody>::cons(
          EpitopeAntibody{eplet_65QIA, UINT64_C(9000), true},
          List<EpitopeAntibody>::cons(
              EpitopeAntibody{eplet_142T, UINT64_C(6000), false},
              List<EpitopeAntibody>::nil())),
      UINT64_C(95), UINT64_C(98), UINT64_C(5)};
  static inline const CrossmatchWithUncertainty good_crossmatch =
      CrossmatchWithUncertainty{CrossmatchResult::XM_COMPATIBLE, UINT64_C(1),
                                TestConfidence::CONFIDENCE_HIGH};
  static inline const CrossmatchWithUncertainty bad_crossmatch =
      CrossmatchWithUncertainty{CrossmatchResult::XM_INCOMPATIBLE, UINT64_C(1),
                                TestConfidence::CONFIDENCE_HIGH};
  static bool risk_acceptable(TransplantAcceptability a);
  static inline const bool sample_virtual_zero_negative = []() {
    switch (classify_mfi_safe(validated_luminex, UINT64_C(0))) {
    case MFIStrength::MFI_NEGATIVE: {
      return true;
    }
    default: {
      return false;
    }
    }
  }();
  static inline const uint64_t sample_dedup_count =
      epitope_dedup(typing_epitopes(donor_hla)).length();
  static inline const bool sample_weak_acceptability = []() {
    switch (full_virtual_crossmatch_safe(validated_luminex, weak_profile,
                                         donor_hla)) {
    case TransplantAcceptability::ACCEPTABLE_WITH_DESENSITIZATION: {
      return true;
    }
    default: {
      return false;
    }
    }
  }();
  static inline const bool sample_strong_absolute_contra = []() {
    switch (full_virtual_crossmatch_safe(validated_luminex, strong_profile,
                                         donor_hla)) {
    case TransplantAcceptability::ABSOLUTE_CONTRAINDICATION: {
      return true;
    }
    default: {
      return false;
    }
    }
  }();
  static inline const bool sample_strong_has_complement_fixing_dsa =
      has_complement_fixing_dsa(strong_profile, donor_hla);
  static inline const uint64_t sample_strong_max_mfi =
      max_dsa_mfi(strong_profile, donor_hla);
  static inline const uint64_t sample_lab_id =
      validated_luminex.vmc_config.mfi_cfg_lab_id;
  static inline const bool sample_order_created = []() -> bool {
    auto _cs = create_safe_transfusion_order(
        UINT64_C(100), UINT64_C(200),
        risk_acceptable(full_virtual_crossmatch_safe(validated_luminex,
                                                     weak_profile, donor_hla)),
        good_crossmatch, UINT64_C(0), UINT64_C(1000), UINT64_C(77), false);
    if (_cs.has_value()) {
      const SafeTransfusionOrder &_x = *_cs;
      return true;
    } else {
      return false;
    }
  }();
  static inline const bool sample_order_blocked = []() -> bool {
    auto _cs = create_safe_transfusion_order(
        UINT64_C(100), UINT64_C(201),
        risk_acceptable(full_virtual_crossmatch_safe(
            validated_luminex, strong_profile, donor_hla)),
        bad_crossmatch, UINT64_C(0), UINT64_C(1000), UINT64_C(77), false);
    if (_cs.has_value()) {
      const SafeTransfusionOrder &_x = *_cs;
      return false;
    } else {
      return true;
    }
  }();
  static inline const bool sample_authorized_order_stays_authorized =
      []() -> bool {
    auto _cs = create_safe_transfusion_order(
        UINT64_C(100), UINT64_C(202), true, good_crossmatch, UINT64_C(100),
        UINT64_C(200), UINT64_C(88), false);
    if (_cs.has_value()) {
      const SafeTransfusionOrder &order = *_cs;
      return transfusion_order_authorized(order, UINT64_C(200));
    } else {
      return false;
    }
  }();
};

#endif // INCLUDED_VALIDATED_VIRTUAL_CROSSMATCH_TRACE
