#include "validated_virtual_crossmatch_trace.h"

bool PeanoNat::eq_dec(uint64_t n, uint64_t m) {
  if (n <= 0) {
    if (m <= 0) {
      return true;
    } else {
      uint64_t _x = m - 1;
      return false;
    }
  } else {
    uint64_t n0 = n - 1;
    if (m <= 0) {
      return false;
    } else {
      uint64_t n1 = m - 1;
      bool s = PeanoNat::eq_dec(n0, n1);
      if (s) {
        return true;
      } else {
        return false;
      }
    }
  }
}

bool ValidatedVirtualCrossmatchTraceCase::hla_locus_eq_dec(
    ValidatedVirtualCrossmatchTraceCase::HLALocus x,
    ValidatedVirtualCrossmatchTraceCase::HLALocus y) {
  switch (x) {
  case HLALocus::LOCUS_A: {
    switch (y) {
    case HLALocus::LOCUS_A: {
      return true;
    }
    default: {
      return false;
    }
    }
    break;
  }
  case HLALocus::LOCUS_B: {
    switch (y) {
    case HLALocus::LOCUS_B: {
      return true;
    }
    default: {
      return false;
    }
    }
    break;
  }
  case HLALocus::LOCUS_DR: {
    switch (y) {
    case HLALocus::LOCUS_DR: {
      return true;
    }
    default: {
      return false;
    }
    }
    break;
  }
  default:
    std::unreachable();
  }
}

bool ValidatedVirtualCrossmatchTraceCase::hla_allele_eq_dec(
    const ValidatedVirtualCrossmatchTraceCase::HLAAllele &x,
    const ValidatedVirtualCrossmatchTraceCase::HLAAllele &y) {
  ValidatedVirtualCrossmatchTraceCase::HLALocus hla_locus0 = x.hla_locus;
  uint64_t hla_group0 = x.hla_group;
  ValidatedVirtualCrossmatchTraceCase::HLALocus hla_locus1 = y.hla_locus;
  uint64_t hla_group1 = y.hla_group;
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

bool ValidatedVirtualCrossmatchTraceCase::hla_allele_eqb(
    const ValidatedVirtualCrossmatchTraceCase::HLAAllele &x,
    const ValidatedVirtualCrossmatchTraceCase::HLAAllele &y) {
  if (hla_allele_eq_dec(x, y)) {
    return true;
  } else {
    return false;
  }
}

bool ValidatedVirtualCrossmatchTraceCase::epitope_eq_dec(
    const ValidatedVirtualCrossmatchTraceCase::HLAEpitope &x,
    const ValidatedVirtualCrossmatchTraceCase::HLAEpitope &y) {
  uint64_t epitope_id0 = x.epitope_id;
  ValidatedVirtualCrossmatchTraceCase::HLALocus epitope_locus0 =
      x.epitope_locus;
  bool epitope_immunogenic0 = x.epitope_immunogenic;
  uint64_t epitope_id1 = y.epitope_id;
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

bool ValidatedVirtualCrossmatchTraceCase::epitope_eqb(
    const ValidatedVirtualCrossmatchTraceCase::HLAEpitope &x,
    const ValidatedVirtualCrossmatchTraceCase::HLAEpitope &y) {
  if (epitope_eq_dec(x, y)) {
    return true;
  } else {
    return false;
  }
}

List<ValidatedVirtualCrossmatchTraceCase::HLAEpitope>
ValidatedVirtualCrossmatchTraceCase::allele_epitopes(
    const ValidatedVirtualCrossmatchTraceCase::HLAAllele &a) {
  switch (a.hla_locus) {
  case HLALocus::LOCUS_A: {
    if (a.hla_group <= 0) {
      return List<ValidatedVirtualCrossmatchTraceCase::HLAEpitope>::nil();
    } else {
      uint64_t n = a.hla_group - 1;
      if (n <= 0) {
        return List<ValidatedVirtualCrossmatchTraceCase::HLAEpitope>::nil();
      } else {
        uint64_t n0 = n - 1;
        if (n0 <= 0) {
          return List<ValidatedVirtualCrossmatchTraceCase::HLAEpitope>::cons(
              eplet_62GE,
              List<ValidatedVirtualCrossmatchTraceCase::HLAEpitope>::cons(
                  eplet_65QIA,
                  List<
                      ValidatedVirtualCrossmatchTraceCase::HLAEpitope>::nil()));
        } else {
          uint64_t n1 = n0 - 1;
          if (n1 <= 0) {
            return List<ValidatedVirtualCrossmatchTraceCase::HLAEpitope>::cons(
                eplet_62GE,
                List<ValidatedVirtualCrossmatchTraceCase::HLAEpitope>::nil());
          } else {
            uint64_t _x = n1 - 1;
            return List<ValidatedVirtualCrossmatchTraceCase::HLAEpitope>::nil();
          }
        }
      }
    }
    break;
  }
  case HLALocus::LOCUS_B: {
    if (a.hla_group <= 0) {
      return List<ValidatedVirtualCrossmatchTraceCase::HLAEpitope>::nil();
    } else {
      uint64_t n = a.hla_group - 1;
      if (n <= 0) {
        return List<ValidatedVirtualCrossmatchTraceCase::HLAEpitope>::nil();
      } else {
        uint64_t n0 = n - 1;
        if (n0 <= 0) {
          return List<ValidatedVirtualCrossmatchTraceCase::HLAEpitope>::nil();
        } else {
          uint64_t n1 = n0 - 1;
          if (n1 <= 0) {
            return List<ValidatedVirtualCrossmatchTraceCase::HLAEpitope>::nil();
          } else {
            uint64_t n2 = n1 - 1;
            if (n2 <= 0) {
              return List<
                  ValidatedVirtualCrossmatchTraceCase::HLAEpitope>::nil();
            } else {
              uint64_t n3 = n2 - 1;
              if (n3 <= 0) {
                return List<
                    ValidatedVirtualCrossmatchTraceCase::HLAEpitope>::nil();
              } else {
                uint64_t n4 = n3 - 1;
                if (n4 <= 0) {
                  return List<
                      ValidatedVirtualCrossmatchTraceCase::HLAEpitope>::nil();
                } else {
                  uint64_t n5 = n4 - 1;
                  if (n5 <= 0) {
                    return List<
                        ValidatedVirtualCrossmatchTraceCase::HLAEpitope>::
                        cons(eplet_142T,
                             List<ValidatedVirtualCrossmatchTraceCase::
                                      HLAEpitope>::nil());
                  } else {
                    uint64_t _x = n5 - 1;
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
    break;
  }
  case HLALocus::LOCUS_DR: {
    if (a.hla_group <= 0) {
      return List<ValidatedVirtualCrossmatchTraceCase::HLAEpitope>::nil();
    } else {
      uint64_t n = a.hla_group - 1;
      if (n <= 0) {
        return List<ValidatedVirtualCrossmatchTraceCase::HLAEpitope>::nil();
      } else {
        uint64_t n0 = n - 1;
        if (n0 <= 0) {
          return List<ValidatedVirtualCrossmatchTraceCase::HLAEpitope>::nil();
        } else {
          uint64_t n1 = n0 - 1;
          if (n1 <= 0) {
            return List<ValidatedVirtualCrossmatchTraceCase::HLAEpitope>::nil();
          } else {
            uint64_t n2 = n1 - 1;
            if (n2 <= 0) {
              return List<ValidatedVirtualCrossmatchTraceCase::HLAEpitope>::
                  cons(eplet_77N,
                       List<ValidatedVirtualCrossmatchTraceCase::HLAEpitope>::
                           nil());
            } else {
              uint64_t _x = n2 - 1;
              return List<
                  ValidatedVirtualCrossmatchTraceCase::HLAEpitope>::nil();
            }
          }
        }
      }
    }
    break;
  }
  default:
    std::unreachable();
  }
}

List<ValidatedVirtualCrossmatchTraceCase::HLAEpitope>
ValidatedVirtualCrossmatchTraceCase::typing_epitopes(
    const ValidatedVirtualCrossmatchTraceCase::HLATyping &t) {
  return t.hla_typed_alleles
      .template flat_map<ValidatedVirtualCrossmatchTraceCase::HLAEpitope>(
          allele_epitopes);
}

List<ValidatedVirtualCrossmatchTraceCase::HLAEpitope>
ValidatedVirtualCrossmatchTraceCase::epitope_dedup(
    const List<ValidatedVirtualCrossmatchTraceCase::HLAEpitope> &l) {
  if (std::holds_alternative<
          typename List<ValidatedVirtualCrossmatchTraceCase::HLAEpitope>::Nil>(
          l.v())) {
    return List<ValidatedVirtualCrossmatchTraceCase::HLAEpitope>::nil();
  } else {
    const auto &[a0, a1] = std::get<
        typename List<ValidatedVirtualCrossmatchTraceCase::HLAEpitope>::Cons>(
        l.v());
    const List<ValidatedVirtualCrossmatchTraceCase::HLAEpitope> &a1_value = *a1;
    if (a1_value.existsb(
            [=](ValidatedVirtualCrossmatchTraceCase::HLAEpitope _x0) mutable
                -> bool { return epitope_eqb(a0, _x0); })) {
      return epitope_dedup(a1_value);
    } else {
      return List<ValidatedVirtualCrossmatchTraceCase::HLAEpitope>::cons(
          a0, epitope_dedup(a1_value));
    }
  }
}

bool ValidatedVirtualCrossmatchTraceCase::mfi_config_valid(
    const ValidatedVirtualCrossmatchTraceCase::MFIThresholdConfig &cfg) {
  return ((cfg.mfi_cfg_negative < cfg.mfi_cfg_weak_positive &&
           cfg.mfi_cfg_weak_positive < cfg.mfi_cfg_moderate) &&
          cfg.mfi_cfg_moderate < cfg.mfi_cfg_strong);
}

ValidatedVirtualCrossmatchTraceCase::MFIStrength
ValidatedVirtualCrossmatchTraceCase::classify_mfi_with_config(
    const ValidatedVirtualCrossmatchTraceCase::MFIThresholdConfig &cfg,
    uint64_t mfi) {
  if (mfi <= cfg.mfi_cfg_negative) {
    return MFIStrength::MFI_NEGATIVE;
  } else {
    if (mfi <= cfg.mfi_cfg_weak_positive) {
      return MFIStrength::MFI_WEAKPOSITIVE;
    } else {
      if (mfi <= cfg.mfi_cfg_moderate) {
        return MFIStrength::MFI_MODERATE;
      } else {
        if (mfi <= cfg.mfi_cfg_strong) {
          return MFIStrength::MFI_STRONG;
        } else {
          return MFIStrength::MFI_VERYSTRONG;
        }
      }
    }
  }
}

ValidatedVirtualCrossmatchTraceCase::MFIStrength
ValidatedVirtualCrossmatchTraceCase::classify_mfi_safe(
    const ValidatedVirtualCrossmatchTraceCase::ValidatedMFIConfig &vcfg,
    uint64_t mfi) {
  return classify_mfi_with_config(vcfg.vmc_config, mfi);
}

uint64_t ValidatedVirtualCrossmatchTraceCase::max_dsa_mfi(
    const ValidatedVirtualCrossmatchTraceCase::VirtualXMProfile &recipient,
    const ValidatedVirtualCrossmatchTraceCase::HLATyping &donor) {
  List<ValidatedVirtualCrossmatchTraceCase::HLAEpitope> donor_epitopes =
      epitope_dedup(typing_epitopes(donor));
  return recipient.vxm_epitope_abs.template fold_left<uint64_t>(
      [=](uint64_t acc,
          const ValidatedVirtualCrossmatchTraceCase::EpitopeAntibody
              &ab) mutable {
        if (donor_epitopes.existsb(
                [=](ValidatedVirtualCrossmatchTraceCase::HLAEpitope _x0) mutable
                    -> bool { return epitope_eqb(ab.ab_epitope, _x0); })) {
          return std::max(acc, ab.ab_mfi);
        } else {
          return acc;
        }
      },
      UINT64_C(0));
}

bool ValidatedVirtualCrossmatchTraceCase::has_complement_fixing_dsa(
    const ValidatedVirtualCrossmatchTraceCase::VirtualXMProfile &recipient,
    const ValidatedVirtualCrossmatchTraceCase::HLATyping &donor) {
  List<ValidatedVirtualCrossmatchTraceCase::HLAEpitope> donor_epitopes =
      epitope_dedup(typing_epitopes(donor));
  return recipient.vxm_epitope_abs.existsb(
      [=](const ValidatedVirtualCrossmatchTraceCase::EpitopeAntibody
              &ab) mutable {
        return (
            (ab.ab_complement_fixing && mfi_negative_threshold < ab.ab_mfi) &&
            donor_epitopes.existsb(
                [=](ValidatedVirtualCrossmatchTraceCase::HLAEpitope _x0) mutable
                    -> bool { return epitope_eqb(ab.ab_epitope, _x0); }));
      });
}

ValidatedVirtualCrossmatchTraceCase::VirtualXMResult
ValidatedVirtualCrossmatchTraceCase::virtual_crossmatch_safe(
    const ValidatedVirtualCrossmatchTraceCase::ValidatedMFIConfig &vcfg,
    const ValidatedVirtualCrossmatchTraceCase::VirtualXMProfile &recipient,
    const ValidatedVirtualCrossmatchTraceCase::HLATyping &donor) {
  uint64_t max_mfi = max_dsa_mfi(recipient, donor);
  switch (classify_mfi_safe(vcfg, max_mfi)) {
  case MFIStrength::MFI_NEGATIVE: {
    return VirtualXMResult::VXM_NEGATIVE;
  }
  case MFIStrength::MFI_WEAKPOSITIVE: {
    return VirtualXMResult::VXM_WEAKPOSITIVE;
  }
  case MFIStrength::MFI_MODERATE: {
    return VirtualXMResult::VXM_POSITIVE;
  }
  default: {
    return VirtualXMResult::VXM_STRONGPOSITIVE;
  }
  }
}

ValidatedVirtualCrossmatchTraceCase::TransplantAcceptability
ValidatedVirtualCrossmatchTraceCase::transplant_acceptability(
    ValidatedVirtualCrossmatchTraceCase::VirtualXMResult vxm,
    bool complement_fixing_dsa) {
  switch (vxm) {
  case VirtualXMResult::VXM_NEGATIVE: {
    return TransplantAcceptability::ACCEPTABLE;
  }
  case VirtualXMResult::VXM_WEAKPOSITIVE: {
    if (complement_fixing_dsa) {
      return TransplantAcceptability::UNACCEPTABLE_HIGH_RISK;
    } else {
      return TransplantAcceptability::ACCEPTABLE_WITH_DESENSITIZATION;
    }
    break;
  }
  case VirtualXMResult::VXM_POSITIVE: {
    return TransplantAcceptability::UNACCEPTABLE_HIGH_RISK;
  }
  case VirtualXMResult::VXM_STRONGPOSITIVE: {
    return TransplantAcceptability::ABSOLUTE_CONTRAINDICATION;
  }
  default:
    std::unreachable();
  }
}

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

bool ValidatedVirtualCrossmatchTraceCase::safe_to_release(
    const ValidatedVirtualCrossmatchTraceCase::CrossmatchWithUncertainty &xm) {
  switch (xm.xmu_result) {
  case CrossmatchResult::XM_COMPATIBLE: {
    switch (xm.xmu_confidence) {
    case TestConfidence::CONFIDENCE_LOW: {
      return false;
    }
    default: {
      return true;
    }
    }
    break;
  }
  default: {
    return false;
  }
  }
}

bool ValidatedVirtualCrossmatchTraceCase::order_sample_valid(
    uint64_t collection_time, uint64_t current_time) {
  return (((current_time - collection_time) > current_time
               ? 0
               : (current_time - collection_time))) <=
         (UINT64_C(72) * UINT64_C(3600));
}

bool ValidatedVirtualCrossmatchTraceCase::transfusion_order_authorized(
    const ValidatedVirtualCrossmatchTraceCase::SafeTransfusionOrder &order,
    uint64_t current_time) {
  bool compat_ok = order.sto_compatibility_check;
  bool xm_ok = safe_to_release(order.sto_crossmatch);
  bool sample_ok =
      order_sample_valid(order.sto_sample_collection_time, current_time);
  bool emergency = order.sto_emergency_release;
  return (((compat_ok && xm_ok) && sample_ok) || emergency);
}

std::optional<ValidatedVirtualCrossmatchTraceCase::SafeTransfusionOrder>
ValidatedVirtualCrossmatchTraceCase::create_safe_transfusion_order(
    uint64_t recipient_id, uint64_t product_id, bool compat_result,
    ValidatedVirtualCrossmatchTraceCase::CrossmatchWithUncertainty xm,
    uint64_t sample_time, uint64_t current_time, uint64_t authorizer,
    bool is_emergency) {
  ValidatedVirtualCrossmatchTraceCase::SafeTransfusionOrder order =
      SafeTransfusionOrder{recipient_id, product_id, compat_result, xm,
                           sample_time,  authorizer, is_emergency};
  if (transfusion_order_authorized(order, current_time)) {
    return std::make_optional<
        ValidatedVirtualCrossmatchTraceCase::SafeTransfusionOrder>(
        std::move(order));
  } else {
    return std::optional<
        ValidatedVirtualCrossmatchTraceCase::SafeTransfusionOrder>();
  }
}

bool ValidatedVirtualCrossmatchTraceCase::risk_acceptable(
    ValidatedVirtualCrossmatchTraceCase::TransplantAcceptability a) {
  switch (a) {
  case TransplantAcceptability::ACCEPTABLE: {
    return true;
  }
  case TransplantAcceptability::ACCEPTABLE_WITH_DESENSITIZATION: {
    return true;
  }
  default: {
    return false;
  }
  }
}

bool Bool::bool_dec(bool b1, bool b2) {
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
