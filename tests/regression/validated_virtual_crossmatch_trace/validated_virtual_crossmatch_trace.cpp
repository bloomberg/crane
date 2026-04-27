#include <validated_virtual_crossmatch_trace.h>

#include <algorithm>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) bool PeanoNat::eq_dec(const unsigned int &n,
                                            const unsigned int &m) {
  if (n <= 0) {
    if (m <= 0) {
      return true;
    } else {
      unsigned int _x = m - 1;
      return false;
    }
  } else {
    unsigned int n0 = n - 1;
    if (m <= 0) {
      return false;
    } else {
      unsigned int n1 = m - 1;
      bool s = PeanoNat::eq_dec(n0, n1);
      if (s) {
        return true;
      } else {
        return false;
      }
    }
  }
}

__attribute__((pure)) bool
ValidatedVirtualCrossmatchTraceCase::hla_locus_eq_dec(
    const ValidatedVirtualCrossmatchTraceCase::HLALocus x,
    const ValidatedVirtualCrossmatchTraceCase::HLALocus y) {
  switch (x) {
  case HLALocus::e_LOCUS_A: {
    switch (y) {
    case HLALocus::e_LOCUS_A: {
      return true;
    }
    default: {
      return false;
    }
    }
  }
  case HLALocus::e_LOCUS_B: {
    switch (y) {
    case HLALocus::e_LOCUS_B: {
      return true;
    }
    default: {
      return false;
    }
    }
  }
  case HLALocus::e_LOCUS_DR: {
    switch (y) {
    case HLALocus::e_LOCUS_DR: {
      return true;
    }
    default: {
      return false;
    }
    }
  }
  default:
    std::unreachable();
  }
}

__attribute__((pure)) bool
ValidatedVirtualCrossmatchTraceCase::hla_allele_eq_dec(
    const ValidatedVirtualCrossmatchTraceCase::HLAAllele &x,
    const ValidatedVirtualCrossmatchTraceCase::HLAAllele &y) {
  ValidatedVirtualCrossmatchTraceCase::HLALocus hla_locus0 = x.hla_locus;
  unsigned int hla_group0 = x.hla_group;
  ValidatedVirtualCrossmatchTraceCase::HLALocus hla_locus1 = y.hla_locus;
  unsigned int hla_group1 = y.hla_group;
  if (hla_locus_eq_dec(hla_locus0, hla_locus1)) {
    if (PeanoNat::eq_dec(hla_group0, hla_group1)) {
      return true;
    } else {
      return false;
    }
  } else {
    return false;
  }
}

__attribute__((pure)) bool ValidatedVirtualCrossmatchTraceCase::hla_allele_eqb(
    const ValidatedVirtualCrossmatchTraceCase::HLAAllele &x,
    const ValidatedVirtualCrossmatchTraceCase::HLAAllele &y) {
  if (hla_allele_eq_dec(x, y)) {
    return true;
  } else {
    return false;
  }
}

__attribute__((pure)) bool ValidatedVirtualCrossmatchTraceCase::epitope_eq_dec(
    const ValidatedVirtualCrossmatchTraceCase::HLAEpitope &x,
    const ValidatedVirtualCrossmatchTraceCase::HLAEpitope &y) {
  unsigned int epitope_id0 = x.epitope_id;
  ValidatedVirtualCrossmatchTraceCase::HLALocus epitope_locus0 =
      x.epitope_locus;
  bool epitope_immunogenic0 = x.epitope_immunogenic;
  unsigned int epitope_id1 = y.epitope_id;
  ValidatedVirtualCrossmatchTraceCase::HLALocus epitope_locus1 =
      y.epitope_locus;
  bool epitope_immunogenic1 = y.epitope_immunogenic;
  if (PeanoNat::eq_dec(epitope_id0, epitope_id1)) {
    if (hla_locus_eq_dec(epitope_locus0, epitope_locus1)) {
      if (Bool::bool_dec(epitope_immunogenic0, epitope_immunogenic1)) {
        return true;
      } else {
        return false;
      }
    } else {
      return false;
    }
  } else {
    return false;
  }
}

__attribute__((pure)) bool ValidatedVirtualCrossmatchTraceCase::epitope_eqb(
    const ValidatedVirtualCrossmatchTraceCase::HLAEpitope &x,
    const ValidatedVirtualCrossmatchTraceCase::HLAEpitope &y) {
  if (epitope_eq_dec(x, y)) {
    return true;
  } else {
    return false;
  }
}

__attribute__((pure)) List<ValidatedVirtualCrossmatchTraceCase::HLAEpitope>
ValidatedVirtualCrossmatchTraceCase::allele_epitopes(
    const ValidatedVirtualCrossmatchTraceCase::HLAAllele &a) {
  switch (a.hla_locus) {
  case HLALocus::e_LOCUS_A: {
    if (a.hla_group <= 0) {
      return List<ValidatedVirtualCrossmatchTraceCase::HLAEpitope>::nil();
    } else {
      unsigned int n = a.hla_group - 1;
      if (n <= 0) {
        return List<ValidatedVirtualCrossmatchTraceCase::HLAEpitope>::nil();
      } else {
        unsigned int n0 = n - 1;
        if (n0 <= 0) {
          return List<ValidatedVirtualCrossmatchTraceCase::HLAEpitope>::cons(
              eplet_62GE,
              List<ValidatedVirtualCrossmatchTraceCase::HLAEpitope>::cons(
                  eplet_65QIA,
                  List<
                      ValidatedVirtualCrossmatchTraceCase::HLAEpitope>::nil()));
        } else {
          unsigned int n1 = n0 - 1;
          if (n1 <= 0) {
            return List<ValidatedVirtualCrossmatchTraceCase::HLAEpitope>::cons(
                eplet_62GE,
                List<ValidatedVirtualCrossmatchTraceCase::HLAEpitope>::nil());
          } else {
            unsigned int _x = n1 - 1;
            return List<ValidatedVirtualCrossmatchTraceCase::HLAEpitope>::nil();
          }
        }
      }
    }
  }
  case HLALocus::e_LOCUS_B: {
    if (a.hla_group <= 0) {
      return List<ValidatedVirtualCrossmatchTraceCase::HLAEpitope>::nil();
    } else {
      unsigned int n = a.hla_group - 1;
      if (n <= 0) {
        return List<ValidatedVirtualCrossmatchTraceCase::HLAEpitope>::nil();
      } else {
        unsigned int n0 = n - 1;
        if (n0 <= 0) {
          return List<ValidatedVirtualCrossmatchTraceCase::HLAEpitope>::nil();
        } else {
          unsigned int n1 = n0 - 1;
          if (n1 <= 0) {
            return List<ValidatedVirtualCrossmatchTraceCase::HLAEpitope>::nil();
          } else {
            unsigned int n2 = n1 - 1;
            if (n2 <= 0) {
              return List<
                  ValidatedVirtualCrossmatchTraceCase::HLAEpitope>::nil();
            } else {
              unsigned int n3 = n2 - 1;
              if (n3 <= 0) {
                return List<
                    ValidatedVirtualCrossmatchTraceCase::HLAEpitope>::nil();
              } else {
                unsigned int n4 = n3 - 1;
                if (n4 <= 0) {
                  return List<
                      ValidatedVirtualCrossmatchTraceCase::HLAEpitope>::nil();
                } else {
                  unsigned int n5 = n4 - 1;
                  if (n5 <= 0) {
                    return List<
                        ValidatedVirtualCrossmatchTraceCase::HLAEpitope>::
                        cons(eplet_142T,
                             List<ValidatedVirtualCrossmatchTraceCase::
                                      HLAEpitope>::nil());
                  } else {
                    unsigned int _x = n5 - 1;
                    return List<
                        ValidatedVirtualCrossmatchTraceCase::HLAEpitope>::nil();
                  }
                }
              }
            }
          }
        }
      }
    }
  }
  case HLALocus::e_LOCUS_DR: {
    if (a.hla_group <= 0) {
      return List<ValidatedVirtualCrossmatchTraceCase::HLAEpitope>::nil();
    } else {
      unsigned int n = a.hla_group - 1;
      if (n <= 0) {
        return List<ValidatedVirtualCrossmatchTraceCase::HLAEpitope>::nil();
      } else {
        unsigned int n0 = n - 1;
        if (n0 <= 0) {
          return List<ValidatedVirtualCrossmatchTraceCase::HLAEpitope>::nil();
        } else {
          unsigned int n1 = n0 - 1;
          if (n1 <= 0) {
            return List<ValidatedVirtualCrossmatchTraceCase::HLAEpitope>::nil();
          } else {
            unsigned int n2 = n1 - 1;
            if (n2 <= 0) {
              return List<ValidatedVirtualCrossmatchTraceCase::HLAEpitope>::
                  cons(eplet_77N,
                       List<ValidatedVirtualCrossmatchTraceCase::HLAEpitope>::
                           nil());
            } else {
              unsigned int _x = n2 - 1;
              return List<
                  ValidatedVirtualCrossmatchTraceCase::HLAEpitope>::nil();
            }
          }
        }
      }
    }
  }
  default:
    std::unreachable();
  }
}

__attribute__((pure)) List<ValidatedVirtualCrossmatchTraceCase::HLAEpitope>
ValidatedVirtualCrossmatchTraceCase::typing_epitopes(
    const ValidatedVirtualCrossmatchTraceCase::HLATyping &t) {
  return t.hla_typed_alleles
      .template flat_map<ValidatedVirtualCrossmatchTraceCase::HLAEpitope>(
          allele_epitopes);
}

__attribute__((pure)) List<ValidatedVirtualCrossmatchTraceCase::HLAEpitope>
ValidatedVirtualCrossmatchTraceCase::epitope_dedup(
    const List<ValidatedVirtualCrossmatchTraceCase::HLAEpitope> &l) {
  if (std::holds_alternative<
          typename List<ValidatedVirtualCrossmatchTraceCase::HLAEpitope>::Nil>(
          l.v())) {
    return List<ValidatedVirtualCrossmatchTraceCase::HLAEpitope>::nil();
  } else {
    const auto &[d_a0, d_a1] = std::get<
        typename List<ValidatedVirtualCrossmatchTraceCase::HLAEpitope>::Cons>(
        l.v());
    List<ValidatedVirtualCrossmatchTraceCase::HLAEpitope> d_a1_value =
        List<HLAEpitope>(*(d_a1));
    if (d_a1_value.existsb(
            [=](ValidatedVirtualCrossmatchTraceCase::HLAEpitope _x0) mutable
                -> bool { return epitope_eqb(d_a0, _x0); })) {
      return epitope_dedup(d_a1_value);
    } else {
      return List<ValidatedVirtualCrossmatchTraceCase::HLAEpitope>::cons(
          d_a0, epitope_dedup(d_a1_value));
    }
  }
}

__attribute__((pure)) bool
ValidatedVirtualCrossmatchTraceCase::mfi_config_valid(
    const ValidatedVirtualCrossmatchTraceCase::MFIThresholdConfig &cfg) {
  return ((cfg.mfi_cfg_negative < cfg.mfi_cfg_weak_positive &&
           cfg.mfi_cfg_weak_positive < cfg.mfi_cfg_moderate) &&
          cfg.mfi_cfg_moderate < cfg.mfi_cfg_strong);
}

__attribute__((pure)) ValidatedVirtualCrossmatchTraceCase::MFIStrength
ValidatedVirtualCrossmatchTraceCase::classify_mfi_with_config(
    const ValidatedVirtualCrossmatchTraceCase::MFIThresholdConfig &cfg,
    const unsigned int &mfi) {
  if (mfi <= cfg.mfi_cfg_negative) {
    return MFIStrength::e_MFI_NEGATIVE;
  } else {
    if (mfi <= cfg.mfi_cfg_weak_positive) {
      return MFIStrength::e_MFI_WEAKPOSITIVE;
    } else {
      if (mfi <= cfg.mfi_cfg_moderate) {
        return MFIStrength::e_MFI_MODERATE;
      } else {
        if (mfi <= cfg.mfi_cfg_strong) {
          return MFIStrength::e_MFI_STRONG;
        } else {
          return MFIStrength::e_MFI_VERYSTRONG;
        }
      }
    }
  }
}

__attribute__((pure)) ValidatedVirtualCrossmatchTraceCase::MFIStrength
ValidatedVirtualCrossmatchTraceCase::classify_mfi_safe(
    const ValidatedVirtualCrossmatchTraceCase::ValidatedMFIConfig &vcfg,
    const unsigned int &mfi) {
  return classify_mfi_with_config(vcfg.vmc_config, mfi);
}

__attribute__((pure)) unsigned int
ValidatedVirtualCrossmatchTraceCase::max_dsa_mfi(
    const ValidatedVirtualCrossmatchTraceCase::VirtualXMProfile &recipient,
    const ValidatedVirtualCrossmatchTraceCase::HLATyping &donor) {
  List<ValidatedVirtualCrossmatchTraceCase::HLAEpitope> donor_epitopes =
      epitope_dedup(typing_epitopes(donor));
  return recipient.vxm_epitope_abs.template fold_left<unsigned int>(
      [=](unsigned int acc,
          ValidatedVirtualCrossmatchTraceCase::EpitopeAntibody ab) mutable {
        if (donor_epitopes.existsb(
                [=](ValidatedVirtualCrossmatchTraceCase::HLAEpitope _x0) mutable
                    -> bool { return epitope_eqb(ab.ab_epitope, _x0); })) {
          return std::max(acc, ab.ab_mfi);
        } else {
          return acc;
        }
      },
      0u);
}

__attribute__((pure)) bool
ValidatedVirtualCrossmatchTraceCase::has_complement_fixing_dsa(
    const ValidatedVirtualCrossmatchTraceCase::VirtualXMProfile &recipient,
    const ValidatedVirtualCrossmatchTraceCase::HLATyping &donor) {
  List<ValidatedVirtualCrossmatchTraceCase::HLAEpitope> donor_epitopes =
      epitope_dedup(typing_epitopes(donor));
  return recipient.vxm_epitope_abs.existsb(
      [=](ValidatedVirtualCrossmatchTraceCase::EpitopeAntibody ab) mutable {
        return (
            (ab.ab_complement_fixing && mfi_negative_threshold < ab.ab_mfi) &&
            donor_epitopes.existsb(
                [=](ValidatedVirtualCrossmatchTraceCase::HLAEpitope _x0) mutable
                    -> bool { return epitope_eqb(ab.ab_epitope, _x0); }));
      });
}

__attribute__((pure)) ValidatedVirtualCrossmatchTraceCase::VirtualXMResult
ValidatedVirtualCrossmatchTraceCase::virtual_crossmatch_safe(
    const ValidatedVirtualCrossmatchTraceCase::ValidatedMFIConfig &vcfg,
    const ValidatedVirtualCrossmatchTraceCase::VirtualXMProfile &recipient,
    const ValidatedVirtualCrossmatchTraceCase::HLATyping &donor) {
  unsigned int max_mfi = max_dsa_mfi(recipient, donor);
  switch (classify_mfi_safe(vcfg, max_mfi)) {
  case MFIStrength::e_MFI_NEGATIVE: {
    return VirtualXMResult::e_VXM_NEGATIVE;
  }
  case MFIStrength::e_MFI_WEAKPOSITIVE: {
    return VirtualXMResult::e_VXM_WEAKPOSITIVE;
  }
  case MFIStrength::e_MFI_MODERATE: {
    return VirtualXMResult::e_VXM_POSITIVE;
  }
  default: {
    return VirtualXMResult::e_VXM_STRONGPOSITIVE;
  }
  }
}

__attribute__((pure))
ValidatedVirtualCrossmatchTraceCase::TransplantAcceptability
ValidatedVirtualCrossmatchTraceCase::transplant_acceptability(
    const ValidatedVirtualCrossmatchTraceCase::VirtualXMResult vxm,
    const bool &complement_fixing_dsa) {
  switch (vxm) {
  case VirtualXMResult::e_VXM_NEGATIVE: {
    return TransplantAcceptability::e_ACCEPTABLE;
  }
  case VirtualXMResult::e_VXM_WEAKPOSITIVE: {
    if (complement_fixing_dsa) {
      return TransplantAcceptability::e_UNACCEPTABLE_HIGH_RISK;
    } else {
      return TransplantAcceptability::e_ACCEPTABLE_WITH_DESENSITIZATION;
    }
  }
  case VirtualXMResult::e_VXM_POSITIVE: {
    return TransplantAcceptability::e_UNACCEPTABLE_HIGH_RISK;
  }
  case VirtualXMResult::e_VXM_STRONGPOSITIVE: {
    return TransplantAcceptability::e_ABSOLUTE_CONTRAINDICATION;
  }
  default:
    std::unreachable();
  }
}

__attribute__((pure))
ValidatedVirtualCrossmatchTraceCase::TransplantAcceptability
ValidatedVirtualCrossmatchTraceCase::full_virtual_crossmatch_safe(
    const ValidatedVirtualCrossmatchTraceCase::ValidatedMFIConfig &vcfg,
    const ValidatedVirtualCrossmatchTraceCase::VirtualXMProfile &recipient,
    const ValidatedVirtualCrossmatchTraceCase::HLATyping &donor) {
  ValidatedVirtualCrossmatchTraceCase::VirtualXMResult vxm =
      virtual_crossmatch_safe(vcfg, recipient, donor);
  bool cf = has_complement_fixing_dsa(recipient, donor);
  return transplant_acceptability(vxm, cf);
}

__attribute__((pure)) bool ValidatedVirtualCrossmatchTraceCase::safe_to_release(
    const ValidatedVirtualCrossmatchTraceCase::CrossmatchWithUncertainty &xm) {
  switch (xm.xmu_result) {
  case CrossmatchResult::e_XM_COMPATIBLE: {
    switch (xm.xmu_confidence) {
    case TestConfidence::e_CONFIDENCE_LOW: {
      return false;
    }
    default: {
      return true;
    }
    }
  }
  default: {
    return false;
  }
  }
}

__attribute__((pure)) bool
ValidatedVirtualCrossmatchTraceCase::order_sample_valid(
    const unsigned int &collection_time, const unsigned int &current_time) {
  return (((current_time - collection_time) > current_time
               ? 0
               : (current_time - collection_time))) <= (72u * 3600u);
}

__attribute__((pure)) bool
ValidatedVirtualCrossmatchTraceCase::transfusion_order_authorized(
    const ValidatedVirtualCrossmatchTraceCase::SafeTransfusionOrder &order,
    const unsigned int &current_time) {
  bool compat_ok = order.sto_compatibility_check;
  bool xm_ok = safe_to_release(order.sto_crossmatch);
  bool sample_ok =
      order_sample_valid(order.sto_sample_collection_time, current_time);
  bool emergency = order.sto_emergency_release;
  return (((compat_ok && xm_ok) && sample_ok) || emergency);
}

__attribute__((pure))
std::optional<ValidatedVirtualCrossmatchTraceCase::SafeTransfusionOrder>
ValidatedVirtualCrossmatchTraceCase::create_safe_transfusion_order(
    unsigned int recipient_id, unsigned int product_id, bool compat_result,
    ValidatedVirtualCrossmatchTraceCase::CrossmatchWithUncertainty xm,
    unsigned int sample_time, const unsigned int &current_time,
    unsigned int authorizer, bool is_emergency) {
  ValidatedVirtualCrossmatchTraceCase::SafeTransfusionOrder order =
      SafeTransfusionOrder{recipient_id, product_id, compat_result, xm,
                           sample_time,  authorizer, is_emergency};
  if (transfusion_order_authorized(order, current_time)) {
    return std::make_optional<
        ValidatedVirtualCrossmatchTraceCase::SafeTransfusionOrder>(order);
  } else {
    return std::optional<
        ValidatedVirtualCrossmatchTraceCase::SafeTransfusionOrder>();
  }
}

__attribute__((pure)) bool ValidatedVirtualCrossmatchTraceCase::risk_acceptable(
    const ValidatedVirtualCrossmatchTraceCase::TransplantAcceptability a) {
  switch (a) {
  case TransplantAcceptability::e_ACCEPTABLE: {
    return true;
  }
  case TransplantAcceptability::e_ACCEPTABLE_WITH_DESENSITIZATION: {
    return true;
  }
  default: {
    return false;
  }
  }
}

__attribute__((pure)) bool Bool::bool_dec(const bool &b1, const bool &b2) {
  if (b1) {
    if (b2) {
      return true;
    } else {
      return false;
    }
  } else {
    if (b2) {
      return false;
    } else {
      return true;
    }
  }
}

__attribute__((pure)) unsigned int Nat::tail_add(const unsigned int &n,
                                                 unsigned int m) {
  if (n <= 0) {
    return m;
  } else {
    unsigned int n0 = n - 1;
    return Nat::tail_add(n0, (m + 1));
  }
}

__attribute__((pure)) unsigned int
Nat::tail_addmul(unsigned int r, const unsigned int &n, const unsigned int &m) {
  if (n <= 0) {
    return r;
  } else {
    unsigned int n0 = n - 1;
    return Nat::tail_addmul(Nat::tail_add(m, r), n0, m);
  }
}

__attribute__((pure)) unsigned int Nat::tail_mul(const unsigned int &n,
                                                 const unsigned int &m) {
  return Nat::tail_addmul(0u, n, m);
}

__attribute__((pure)) unsigned int Nat::of_uint_acc(const Uint &d,
                                                    unsigned int acc) {
  if (std::holds_alternative<typename Uint::Nil>(d.v())) {
    return acc;
  } else if (std::holds_alternative<typename Uint::D0>(d.v())) {
    const auto &[d_a0] = std::get<typename Uint::D0>(d.v());
    return Nat::of_uint_acc(*(d_a0), Nat::tail_mul(10u, acc));
  } else if (std::holds_alternative<typename Uint::D1>(d.v())) {
    const auto &[d_a0] = std::get<typename Uint::D1>(d.v());
    return Nat::of_uint_acc(*(d_a0), (Nat::tail_mul(10u, acc) + 1));
  } else if (std::holds_alternative<typename Uint::D2>(d.v())) {
    const auto &[d_a0] = std::get<typename Uint::D2>(d.v());
    return Nat::of_uint_acc(*(d_a0), ((Nat::tail_mul(10u, acc) + 1) + 1));
  } else if (std::holds_alternative<typename Uint::D3>(d.v())) {
    const auto &[d_a0] = std::get<typename Uint::D3>(d.v());
    return Nat::of_uint_acc(*(d_a0), (((Nat::tail_mul(10u, acc) + 1) + 1) + 1));
  } else if (std::holds_alternative<typename Uint::D4>(d.v())) {
    const auto &[d_a0] = std::get<typename Uint::D4>(d.v());
    return Nat::of_uint_acc(*(d_a0),
                            ((((Nat::tail_mul(10u, acc) + 1) + 1) + 1) + 1));
  } else if (std::holds_alternative<typename Uint::D5>(d.v())) {
    const auto &[d_a0] = std::get<typename Uint::D5>(d.v());
    return Nat::of_uint_acc(
        *(d_a0), (((((Nat::tail_mul(10u, acc) + 1) + 1) + 1) + 1) + 1));
  } else if (std::holds_alternative<typename Uint::D6>(d.v())) {
    const auto &[d_a0] = std::get<typename Uint::D6>(d.v());
    return Nat::of_uint_acc(
        *(d_a0), ((((((Nat::tail_mul(10u, acc) + 1) + 1) + 1) + 1) + 1) + 1));
  } else if (std::holds_alternative<typename Uint::D7>(d.v())) {
    const auto &[d_a0] = std::get<typename Uint::D7>(d.v());
    return Nat::of_uint_acc(
        *(d_a0),
        (((((((Nat::tail_mul(10u, acc) + 1) + 1) + 1) + 1) + 1) + 1) + 1));
  } else if (std::holds_alternative<typename Uint::D8>(d.v())) {
    const auto &[d_a0] = std::get<typename Uint::D8>(d.v());
    return Nat::of_uint_acc(
        *(d_a0),
        ((((((((Nat::tail_mul(10u, acc) + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
         1));
  } else {
    const auto &[d_a0] = std::get<typename Uint::D9>(d.v());
    return Nat::of_uint_acc(
        *(d_a0),
        (((((((((Nat::tail_mul(10u, acc) + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
          1) +
         1));
  }
}

__attribute__((pure)) unsigned int Nat::of_uint(const Uint &d) {
  return Nat::of_uint_acc(d, 0u);
}

__attribute__((pure)) unsigned int Nat::of_hex_uint_acc(const Uint0 &d,
                                                        unsigned int acc) {
  if (std::holds_alternative<typename Uint0::Nil0>(d.v())) {
    return acc;
  } else if (std::holds_alternative<typename Uint0::D10>(d.v())) {
    const auto &[d_a0] = std::get<typename Uint0::D10>(d.v());
    return Nat::of_hex_uint_acc(*(d_a0), Nat::tail_mul(16u, acc));
  } else if (std::holds_alternative<typename Uint0::D11>(d.v())) {
    const auto &[d_a0] = std::get<typename Uint0::D11>(d.v());
    return Nat::of_hex_uint_acc(*(d_a0), (Nat::tail_mul(16u, acc) + 1));
  } else if (std::holds_alternative<typename Uint0::D12>(d.v())) {
    const auto &[d_a0] = std::get<typename Uint0::D12>(d.v());
    return Nat::of_hex_uint_acc(*(d_a0), ((Nat::tail_mul(16u, acc) + 1) + 1));
  } else if (std::holds_alternative<typename Uint0::D13>(d.v())) {
    const auto &[d_a0] = std::get<typename Uint0::D13>(d.v());
    return Nat::of_hex_uint_acc(*(d_a0),
                                (((Nat::tail_mul(16u, acc) + 1) + 1) + 1));
  } else if (std::holds_alternative<typename Uint0::D14>(d.v())) {
    const auto &[d_a0] = std::get<typename Uint0::D14>(d.v());
    return Nat::of_hex_uint_acc(
        *(d_a0), ((((Nat::tail_mul(16u, acc) + 1) + 1) + 1) + 1));
  } else if (std::holds_alternative<typename Uint0::D15>(d.v())) {
    const auto &[d_a0] = std::get<typename Uint0::D15>(d.v());
    return Nat::of_hex_uint_acc(
        *(d_a0), (((((Nat::tail_mul(16u, acc) + 1) + 1) + 1) + 1) + 1));
  } else if (std::holds_alternative<typename Uint0::D16>(d.v())) {
    const auto &[d_a0] = std::get<typename Uint0::D16>(d.v());
    return Nat::of_hex_uint_acc(
        *(d_a0), ((((((Nat::tail_mul(16u, acc) + 1) + 1) + 1) + 1) + 1) + 1));
  } else if (std::holds_alternative<typename Uint0::D17>(d.v())) {
    const auto &[d_a0] = std::get<typename Uint0::D17>(d.v());
    return Nat::of_hex_uint_acc(
        *(d_a0),
        (((((((Nat::tail_mul(16u, acc) + 1) + 1) + 1) + 1) + 1) + 1) + 1));
  } else if (std::holds_alternative<typename Uint0::D18>(d.v())) {
    const auto &[d_a0] = std::get<typename Uint0::D18>(d.v());
    return Nat::of_hex_uint_acc(
        *(d_a0),
        ((((((((Nat::tail_mul(16u, acc) + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
         1));
  } else if (std::holds_alternative<typename Uint0::D19>(d.v())) {
    const auto &[d_a0] = std::get<typename Uint0::D19>(d.v());
    return Nat::of_hex_uint_acc(
        *(d_a0),
        (((((((((Nat::tail_mul(16u, acc) + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
          1) +
         1));
  } else if (std::holds_alternative<typename Uint0::Da>(d.v())) {
    const auto &[d_a0] = std::get<typename Uint0::Da>(d.v());
    return Nat::of_hex_uint_acc(
        *(d_a0),
        ((((((((((Nat::tail_mul(16u, acc) + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
           1) +
          1) +
         1));
  } else if (std::holds_alternative<typename Uint0::Db>(d.v())) {
    const auto &[d_a0] = std::get<typename Uint0::Db>(d.v());
    return Nat::of_hex_uint_acc(
        *(d_a0),
        (((((((((((Nat::tail_mul(16u, acc) + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
            1) +
           1) +
          1) +
         1));
  } else if (std::holds_alternative<typename Uint0::Dc>(d.v())) {
    const auto &[d_a0] = std::get<typename Uint0::Dc>(d.v());
    return Nat::of_hex_uint_acc(
        *(d_a0),
        ((((((((((((Nat::tail_mul(16u, acc) + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
             1) +
            1) +
           1) +
          1) +
         1));
  } else if (std::holds_alternative<typename Uint0::Dd>(d.v())) {
    const auto &[d_a0] = std::get<typename Uint0::Dd>(d.v());
    return Nat::of_hex_uint_acc(
        *(d_a0),
        (((((((((((((Nat::tail_mul(16u, acc) + 1) + 1) + 1) + 1) + 1) + 1) +
               1) +
              1) +
             1) +
            1) +
           1) +
          1) +
         1));
  } else if (std::holds_alternative<typename Uint0::De>(d.v())) {
    const auto &[d_a0] = std::get<typename Uint0::De>(d.v());
    return Nat::of_hex_uint_acc(
        *(d_a0),
        ((((((((((((((Nat::tail_mul(16u, acc) + 1) + 1) + 1) + 1) + 1) + 1) +
                1) +
               1) +
              1) +
             1) +
            1) +
           1) +
          1) +
         1));
  } else {
    const auto &[d_a0] = std::get<typename Uint0::Df>(d.v());
    return Nat::of_hex_uint_acc(
        *(d_a0),
        (((((((((((((((Nat::tail_mul(16u, acc) + 1) + 1) + 1) + 1) + 1) + 1) +
                 1) +
                1) +
               1) +
              1) +
             1) +
            1) +
           1) +
          1) +
         1));
  }
}

__attribute__((pure)) unsigned int Nat::of_hex_uint(const Uint0 &d) {
  return Nat::of_hex_uint_acc(d, 0u);
}

__attribute__((pure)) unsigned int Nat::of_num_uint(const Uint1 &d) {
  if (std::holds_alternative<typename Uint1::UIntDecimal>(d.v())) {
    const auto &[d_u] = std::get<typename Uint1::UIntDecimal>(d.v());
    return Nat::of_uint(d_u);
  } else {
    const auto &[d_u] = std::get<typename Uint1::UIntHexadecimal>(d.v());
    return Nat::of_hex_uint(d_u);
  }
}
