#include <validated_virtual_crossmatch_trace.h>

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) bool PeanoNat::leb(const unsigned int n,
                                         const unsigned int m) {
  if (n <= 0) {
    return true;
  } else {
    unsigned int n_ = n - 1;
    if (m <= 0) {
      return false;
    } else {
      unsigned int m_ = m - 1;
      return PeanoNat::leb(n_, m_);
    }
  }
}

__attribute__((pure)) bool PeanoNat::ltb(const unsigned int n,
                                         const unsigned int m) {
  return PeanoNat::leb((std::move(n) + 1), m);
}

__attribute__((pure)) unsigned int PeanoNat::max(const unsigned int n,
                                                 const unsigned int m) {
  if (n <= 0) {
    return std::move(m);
  } else {
    unsigned int n_ = n - 1;
    if (m <= 0) {
      return n;
    } else {
      unsigned int m_ = m - 1;
      return (PeanoNat::max(std::move(n_), std::move(m_)) + 1);
    }
  }
}

__attribute__((pure)) bool PeanoNat::eq_dec(const unsigned int n,
                                            const unsigned int m) {
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
      if (std::move(s)) {
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
  return [&](void) {
    switch (x) {
    case HLALocus::e_LOCUS_A: {
      return [&](void) {
        switch (y) {
        case HLALocus::e_LOCUS_A: {
          return true;
        }
        case HLALocus::e_LOCUS_B: {
          return false;
        }
        case HLALocus::e_LOCUS_DR: {
          return false;
        }
        }
      }();
    }
    case HLALocus::e_LOCUS_B: {
      return [&](void) {
        switch (y) {
        case HLALocus::e_LOCUS_A: {
          return false;
        }
        case HLALocus::e_LOCUS_B: {
          return true;
        }
        case HLALocus::e_LOCUS_DR: {
          return false;
        }
        }
      }();
    }
    case HLALocus::e_LOCUS_DR: {
      return [&](void) {
        switch (y) {
        case HLALocus::e_LOCUS_A: {
          return false;
        }
        case HLALocus::e_LOCUS_B: {
          return false;
        }
        case HLALocus::e_LOCUS_DR: {
          return true;
        }
        }
      }();
    }
    }
  }();
}

__attribute__((pure)) bool
ValidatedVirtualCrossmatchTraceCase::hla_allele_eq_dec(
    const std::shared_ptr<ValidatedVirtualCrossmatchTraceCase::HLAAllele> &x,
    const std::shared_ptr<ValidatedVirtualCrossmatchTraceCase::HLAAllele> &y) {
  return [&](void) {
    ValidatedVirtualCrossmatchTraceCase::HLALocus hla_locus0 = x->hla_locus;
    unsigned int hla_group0 = x->hla_group;
    return [&](void) {
      ValidatedVirtualCrossmatchTraceCase::HLALocus hla_locus1 = y->hla_locus;
      unsigned int hla_group1 = y->hla_group;
      if (hla_locus_eq_dec(hla_locus0, hla_locus1)) {
        if (PeanoNat::eq_dec(hla_group0, hla_group1)) {
          return true;
        } else {
          return false;
        }
      } else {
        return false;
      }
    }();
  }();
}

__attribute__((pure)) bool ValidatedVirtualCrossmatchTraceCase::hla_allele_eqb(
    const std::shared_ptr<ValidatedVirtualCrossmatchTraceCase::HLAAllele> &x,
    const std::shared_ptr<ValidatedVirtualCrossmatchTraceCase::HLAAllele> &y) {
  if (hla_allele_eq_dec(x, y)) {
    return true;
  } else {
    return false;
  }
}

__attribute__((pure)) bool ValidatedVirtualCrossmatchTraceCase::epitope_eq_dec(
    const std::shared_ptr<ValidatedVirtualCrossmatchTraceCase::HLAEpitope> &x,
    const std::shared_ptr<ValidatedVirtualCrossmatchTraceCase::HLAEpitope> &y) {
  return [&](void) {
    unsigned int epitope_id0 = x->epitope_id;
    ValidatedVirtualCrossmatchTraceCase::HLALocus epitope_locus0 =
        x->epitope_locus;
    bool epitope_immunogenic0 = x->epitope_immunogenic;
    return [&](void) {
      unsigned int epitope_id1 = y->epitope_id;
      ValidatedVirtualCrossmatchTraceCase::HLALocus epitope_locus1 =
          y->epitope_locus;
      bool epitope_immunogenic1 = y->epitope_immunogenic;
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
    }();
  }();
}

__attribute__((pure)) bool ValidatedVirtualCrossmatchTraceCase::epitope_eqb(
    const std::shared_ptr<ValidatedVirtualCrossmatchTraceCase::HLAEpitope> &x,
    const std::shared_ptr<ValidatedVirtualCrossmatchTraceCase::HLAEpitope> &y) {
  if (epitope_eq_dec(x, y)) {
    return true;
  } else {
    return false;
  }
}

std::shared_ptr<
    List<std::shared_ptr<ValidatedVirtualCrossmatchTraceCase::HLAEpitope>>>
ValidatedVirtualCrossmatchTraceCase::allele_epitopes(
    const std::shared_ptr<ValidatedVirtualCrossmatchTraceCase::HLAAllele> &a) {
  return [&](void) {
    switch (a->hla_locus) {
    case HLALocus::e_LOCUS_A: {
      if (a->hla_group <= 0) {
        return List<std::shared_ptr<
            ValidatedVirtualCrossmatchTraceCase::HLAEpitope>>::nil();
      } else {
        unsigned int n = a->hla_group - 1;
        if (n <= 0) {
          return List<std::shared_ptr<
              ValidatedVirtualCrossmatchTraceCase::HLAEpitope>>::nil();
        } else {
          unsigned int n0 = n - 1;
          if (n0 <= 0) {
            return List<std::shared_ptr<
                ValidatedVirtualCrossmatchTraceCase::HLAEpitope>>::
                cons(eplet_62GE,
                     List<std::shared_ptr<
                         ValidatedVirtualCrossmatchTraceCase::HLAEpitope>>::
                         cons(eplet_65QIA,
                              List<std::shared_ptr<
                                  ValidatedVirtualCrossmatchTraceCase::
                                      HLAEpitope>>::nil()));
          } else {
            unsigned int n1 = n0 - 1;
            if (n1 <= 0) {
              return List<std::shared_ptr<
                  ValidatedVirtualCrossmatchTraceCase::HLAEpitope>>::
                  cons(
                      eplet_62GE,
                      List<std::shared_ptr<ValidatedVirtualCrossmatchTraceCase::
                                               HLAEpitope>>::nil());
            } else {
              unsigned int _x = n1 - 1;
              return List<std::shared_ptr<
                  ValidatedVirtualCrossmatchTraceCase::HLAEpitope>>::nil();
            }
          }
        }
      }
    }
    case HLALocus::e_LOCUS_B: {
      if (a->hla_group <= 0) {
        return List<std::shared_ptr<
            ValidatedVirtualCrossmatchTraceCase::HLAEpitope>>::nil();
      } else {
        unsigned int n = a->hla_group - 1;
        if (n <= 0) {
          return List<std::shared_ptr<
              ValidatedVirtualCrossmatchTraceCase::HLAEpitope>>::nil();
        } else {
          unsigned int n0 = n - 1;
          if (n0 <= 0) {
            return List<std::shared_ptr<
                ValidatedVirtualCrossmatchTraceCase::HLAEpitope>>::nil();
          } else {
            unsigned int n1 = n0 - 1;
            if (n1 <= 0) {
              return List<std::shared_ptr<
                  ValidatedVirtualCrossmatchTraceCase::HLAEpitope>>::nil();
            } else {
              unsigned int n2 = n1 - 1;
              if (n2 <= 0) {
                return List<std::shared_ptr<
                    ValidatedVirtualCrossmatchTraceCase::HLAEpitope>>::nil();
              } else {
                unsigned int n3 = n2 - 1;
                if (n3 <= 0) {
                  return List<std::shared_ptr<
                      ValidatedVirtualCrossmatchTraceCase::HLAEpitope>>::nil();
                } else {
                  unsigned int n4 = n3 - 1;
                  if (n4 <= 0) {
                    return List<std::shared_ptr<
                        ValidatedVirtualCrossmatchTraceCase::HLAEpitope>>::
                        nil();
                  } else {
                    unsigned int n5 = n4 - 1;
                    if (n5 <= 0) {
                      return List<std::shared_ptr<
                          ValidatedVirtualCrossmatchTraceCase::HLAEpitope>>::
                          cons(eplet_142T,
                               List<std::shared_ptr<
                                   ValidatedVirtualCrossmatchTraceCase::
                                       HLAEpitope>>::nil());
                    } else {
                      unsigned int _x = n5 - 1;
                      return List<std::shared_ptr<
                          ValidatedVirtualCrossmatchTraceCase::HLAEpitope>>::
                          nil();
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
      if (a->hla_group <= 0) {
        return List<std::shared_ptr<
            ValidatedVirtualCrossmatchTraceCase::HLAEpitope>>::nil();
      } else {
        unsigned int n = a->hla_group - 1;
        if (n <= 0) {
          return List<std::shared_ptr<
              ValidatedVirtualCrossmatchTraceCase::HLAEpitope>>::nil();
        } else {
          unsigned int n0 = n - 1;
          if (n0 <= 0) {
            return List<std::shared_ptr<
                ValidatedVirtualCrossmatchTraceCase::HLAEpitope>>::nil();
          } else {
            unsigned int n1 = n0 - 1;
            if (n1 <= 0) {
              return List<std::shared_ptr<
                  ValidatedVirtualCrossmatchTraceCase::HLAEpitope>>::nil();
            } else {
              unsigned int n2 = n1 - 1;
              if (n2 <= 0) {
                return List<std::shared_ptr<
                    ValidatedVirtualCrossmatchTraceCase::HLAEpitope>>::
                    cons(eplet_77N,
                         List<std::shared_ptr<
                             ValidatedVirtualCrossmatchTraceCase::HLAEpitope>>::
                             nil());
              } else {
                unsigned int _x = n2 - 1;
                return List<std::shared_ptr<
                    ValidatedVirtualCrossmatchTraceCase::HLAEpitope>>::nil();
              }
            }
          }
        }
      }
    }
    }
  }();
}

std::shared_ptr<
    List<std::shared_ptr<ValidatedVirtualCrossmatchTraceCase::HLAEpitope>>>
ValidatedVirtualCrossmatchTraceCase::typing_epitopes(
    const std::shared_ptr<ValidatedVirtualCrossmatchTraceCase::HLATyping> &t) {
  return t->hla_typed_alleles->template flat_map<
      std::shared_ptr<ValidatedVirtualCrossmatchTraceCase::HLAEpitope>>(
      allele_epitopes);
}

std::shared_ptr<
    List<std::shared_ptr<ValidatedVirtualCrossmatchTraceCase::HLAEpitope>>>
ValidatedVirtualCrossmatchTraceCase::epitope_dedup(
    const std::shared_ptr<
        List<std::shared_ptr<ValidatedVirtualCrossmatchTraceCase::HLAEpitope>>>
        &l) {
  return std::visit(
      Overloaded{
          [](const typename List<std::shared_ptr<
                 ValidatedVirtualCrossmatchTraceCase::HLAEpitope>>::Nil _args)
              -> std::shared_ptr<List<std::shared_ptr<
                  ValidatedVirtualCrossmatchTraceCase::HLAEpitope>>> {
            return List<std::shared_ptr<
                ValidatedVirtualCrossmatchTraceCase::HLAEpitope>>::nil();
          },
          [](const typename List<std::shared_ptr<
                 ValidatedVirtualCrossmatchTraceCase::HLAEpitope>>::Cons _args)
              -> std::shared_ptr<List<std::shared_ptr<
                  ValidatedVirtualCrossmatchTraceCase::HLAEpitope>>> {
            if (_args.d_a1->existsb(
                    [&](const std::shared_ptr<
                        ValidatedVirtualCrossmatchTraceCase::HLAEpitope> &_x0)
                        -> bool { return epitope_eqb(_args.d_a0, _x0); })) {
              return epitope_dedup(_args.d_a1);
            } else {
              return List<std::shared_ptr<
                  ValidatedVirtualCrossmatchTraceCase::HLAEpitope>>::
                  cons(_args.d_a0, epitope_dedup(_args.d_a1));
            }
          }},
      l->v());
}

__attribute__((pure)) bool
ValidatedVirtualCrossmatchTraceCase::mfi_config_valid(
    const std::shared_ptr<
        ValidatedVirtualCrossmatchTraceCase::MFIThresholdConfig> &cfg) {
  return ((PeanoNat::ltb(cfg->mfi_cfg_negative, cfg->mfi_cfg_weak_positive) &&
           PeanoNat::ltb(cfg->mfi_cfg_weak_positive, cfg->mfi_cfg_moderate)) &&
          PeanoNat::ltb(cfg->mfi_cfg_moderate, cfg->mfi_cfg_strong));
}

__attribute__((pure)) ValidatedVirtualCrossmatchTraceCase::MFIStrength
ValidatedVirtualCrossmatchTraceCase::classify_mfi_with_config(
    const std::shared_ptr<
        ValidatedVirtualCrossmatchTraceCase::MFIThresholdConfig> &cfg,
    const unsigned int mfi) {
  if (PeanoNat::leb(mfi, cfg->mfi_cfg_negative)) {
    return MFIStrength::e_MFI_NEGATIVE;
  } else {
    if (PeanoNat::leb(mfi, cfg->mfi_cfg_weak_positive)) {
      return MFIStrength::e_MFI_WEAKPOSITIVE;
    } else {
      if (PeanoNat::leb(mfi, cfg->mfi_cfg_moderate)) {
        return MFIStrength::e_MFI_MODERATE;
      } else {
        if (PeanoNat::leb(mfi, cfg->mfi_cfg_strong)) {
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
    const std::shared_ptr<
        ValidatedVirtualCrossmatchTraceCase::ValidatedMFIConfig> &vcfg,
    const unsigned int mfi) {
  return classify_mfi_with_config(vcfg->vmc_config, mfi);
}

__attribute__((pure)) unsigned int
ValidatedVirtualCrossmatchTraceCase::max_dsa_mfi(
    const std::shared_ptr<ValidatedVirtualCrossmatchTraceCase::VirtualXMProfile>
        &recipient,
    const std::shared_ptr<ValidatedVirtualCrossmatchTraceCase::HLATyping>
        &donor) {
  std::shared_ptr<
      List<std::shared_ptr<ValidatedVirtualCrossmatchTraceCase::HLAEpitope>>>
      donor_epitopes = epitope_dedup(typing_epitopes(donor));
  return recipient->vxm_epitope_abs->template fold_left<unsigned int>(
      [=](unsigned int acc,
          std::shared_ptr<ValidatedVirtualCrossmatchTraceCase::EpitopeAntibody>
              ab) mutable {
        if (donor_epitopes->existsb(
                [&](const std::shared_ptr<
                    ValidatedVirtualCrossmatchTraceCase::HLAEpitope> &_x0)
                    -> bool { return epitope_eqb(ab->ab_epitope, _x0); })) {
          return PeanoNat::max(acc, ab->ab_mfi);
        } else {
          return acc;
        }
      },
      0u);
}

__attribute__((pure)) bool
ValidatedVirtualCrossmatchTraceCase::has_complement_fixing_dsa(
    const std::shared_ptr<ValidatedVirtualCrossmatchTraceCase::VirtualXMProfile>
        &recipient,
    const std::shared_ptr<ValidatedVirtualCrossmatchTraceCase::HLATyping>
        &donor) {
  std::shared_ptr<
      List<std::shared_ptr<ValidatedVirtualCrossmatchTraceCase::HLAEpitope>>>
      donor_epitopes = epitope_dedup(typing_epitopes(donor));
  return recipient->vxm_epitope_abs->existsb(
      [=](std::shared_ptr<ValidatedVirtualCrossmatchTraceCase::EpitopeAntibody>
              ab) mutable {
        return ((ab->ab_complement_fixing &&
                 PeanoNat::ltb(mfi_negative_threshold, ab->ab_mfi)) &&
                donor_epitopes->existsb(
                    [&](const std::shared_ptr<
                        ValidatedVirtualCrossmatchTraceCase::HLAEpitope> &_x0)
                        -> bool { return epitope_eqb(ab->ab_epitope, _x0); }));
      });
}

__attribute__((pure)) ValidatedVirtualCrossmatchTraceCase::VirtualXMResult
ValidatedVirtualCrossmatchTraceCase::virtual_crossmatch_safe(
    const std::shared_ptr<
        ValidatedVirtualCrossmatchTraceCase::ValidatedMFIConfig> &vcfg,
    const std::shared_ptr<ValidatedVirtualCrossmatchTraceCase::VirtualXMProfile>
        &recipient,
    const std::shared_ptr<ValidatedVirtualCrossmatchTraceCase::HLATyping>
        &donor) {
  unsigned int max_mfi = max_dsa_mfi(recipient, donor);
  return [&](void) {
    switch (classify_mfi_safe(vcfg, std::move(max_mfi))) {
    case MFIStrength::e_MFI_NEGATIVE: {
      return VirtualXMResult::e_VXM_NEGATIVE;
    }
    case MFIStrength::e_MFI_WEAKPOSITIVE: {
      return VirtualXMResult::e_VXM_WEAKPOSITIVE;
    }
    case MFIStrength::e_MFI_MODERATE: {
      return VirtualXMResult::e_VXM_POSITIVE;
    }
    case MFIStrength::e_MFI_STRONG: {
      return VirtualXMResult::e_VXM_STRONGPOSITIVE;
    }
    case MFIStrength::e_MFI_VERYSTRONG: {
      return VirtualXMResult::e_VXM_STRONGPOSITIVE;
    }
    }
  }();
}

__attribute__((pure))
ValidatedVirtualCrossmatchTraceCase::TransplantAcceptability
ValidatedVirtualCrossmatchTraceCase::transplant_acceptability(
    const ValidatedVirtualCrossmatchTraceCase::VirtualXMResult vxm,
    const bool complement_fixing_dsa) {
  return [&](void) {
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
    }
  }();
}

__attribute__((pure))
ValidatedVirtualCrossmatchTraceCase::TransplantAcceptability
ValidatedVirtualCrossmatchTraceCase::full_virtual_crossmatch_safe(
    const std::shared_ptr<
        ValidatedVirtualCrossmatchTraceCase::ValidatedMFIConfig> &vcfg,
    const std::shared_ptr<ValidatedVirtualCrossmatchTraceCase::VirtualXMProfile>
        &recipient,
    const std::shared_ptr<ValidatedVirtualCrossmatchTraceCase::HLATyping>
        &donor) {
  ValidatedVirtualCrossmatchTraceCase::VirtualXMResult vxm =
      virtual_crossmatch_safe(vcfg, recipient, donor);
  bool cf = has_complement_fixing_dsa(recipient, donor);
  return transplant_acceptability(vxm, std::move(cf));
}

__attribute__((pure)) bool ValidatedVirtualCrossmatchTraceCase::safe_to_release(
    const std::shared_ptr<
        ValidatedVirtualCrossmatchTraceCase::CrossmatchWithUncertainty> &xm) {
  return [&](void) {
    switch (xm->xmu_result) {
    case CrossmatchResult::e_XM_COMPATIBLE: {
      return [&](void) {
        switch (xm->xmu_confidence) {
        case TestConfidence::e_CONFIDENCE_HIGH: {
          return true;
        }
        case TestConfidence::e_CONFIDENCE_MEDIUM: {
          return true;
        }
        case TestConfidence::e_CONFIDENCE_LOW: {
          return false;
        }
        }
      }();
    }
    case CrossmatchResult::e_XM_INCOMPATIBLE: {
      return false;
    }
    case CrossmatchResult::e_XM_INCONCLUSIVE: {
      return false;
    }
    case CrossmatchResult::e_XM_NOT_DONE: {
      return false;
    }
    }
  }();
}

__attribute__((pure)) bool
ValidatedVirtualCrossmatchTraceCase::order_sample_valid(
    const unsigned int collection_time, const unsigned int current_time) {
  return PeanoNat::leb((((current_time - collection_time) > current_time
                             ? 0
                             : (current_time - collection_time))),
                       (72u * 3600u));
}

__attribute__((pure)) bool
ValidatedVirtualCrossmatchTraceCase::transfusion_order_authorized(
    const std::shared_ptr<
        ValidatedVirtualCrossmatchTraceCase::SafeTransfusionOrder> &order,
    const unsigned int current_time) {
  bool compat_ok = order->sto_compatibility_check;
  bool xm_ok = safe_to_release(order->sto_crossmatch);
  bool sample_ok =
      order_sample_valid(order->sto_sample_collection_time, current_time);
  bool emergency = order->sto_emergency_release;
  return (
      ((std::move(compat_ok) && std::move(xm_ok)) && std::move(sample_ok)) ||
      std::move(emergency));
}

__attribute__((pure)) std::optional<
    std::shared_ptr<ValidatedVirtualCrossmatchTraceCase::SafeTransfusionOrder>>
ValidatedVirtualCrossmatchTraceCase::create_safe_transfusion_order(
    const unsigned int recipient_id, const unsigned int product_id,
    const bool compat_result,
    std::shared_ptr<
        ValidatedVirtualCrossmatchTraceCase::CrossmatchWithUncertainty>
        xm,
    const unsigned int sample_time, const unsigned int current_time,
    const unsigned int authorizer, const bool is_emergency) {
  std::shared_ptr<ValidatedVirtualCrossmatchTraceCase::SafeTransfusionOrder>
      order = std::make_shared<
          ValidatedVirtualCrossmatchTraceCase::SafeTransfusionOrder>(
          SafeTransfusionOrder{std::move(recipient_id), std::move(product_id),
                               std::move(compat_result), std::move(xm),
                               std::move(sample_time), std::move(authorizer),
                               std::move(is_emergency)});
  if (transfusion_order_authorized(order, current_time)) {
    return std::make_optional<std::shared_ptr<
        ValidatedVirtualCrossmatchTraceCase::SafeTransfusionOrder>>(
        std::move(order));
  } else {
    return std::optional<std::shared_ptr<
        ValidatedVirtualCrossmatchTraceCase::SafeTransfusionOrder>>();
  }
}

__attribute__((pure)) bool ValidatedVirtualCrossmatchTraceCase::risk_acceptable(
    const ValidatedVirtualCrossmatchTraceCase::TransplantAcceptability a) {
  return [&](void) {
    switch (a) {
    case TransplantAcceptability::e_ACCEPTABLE: {
      return true;
    }
    case TransplantAcceptability::e_ACCEPTABLE_WITH_DESENSITIZATION: {
      return true;
    }
    case TransplantAcceptability::e_UNACCEPTABLE_HIGH_RISK: {
      return false;
    }
    case TransplantAcceptability::e_ABSOLUTE_CONTRAINDICATION: {
      return false;
    }
    }
  }();
}

__attribute__((pure)) bool Bool::bool_dec(const bool b1, const bool b2) {
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

__attribute__((pure)) unsigned int Nat::tail_add(const unsigned int n,
                                                 const unsigned int m) {
  if (n <= 0) {
    return std::move(m);
  } else {
    unsigned int n0 = n - 1;
    return Nat::tail_add(std::move(n0), (m + 1));
  }
}

__attribute__((pure)) unsigned int Nat::tail_addmul(const unsigned int r,
                                                    const unsigned int n,
                                                    const unsigned int m) {
  if (n <= 0) {
    return std::move(r);
  } else {
    unsigned int n0 = n - 1;
    return Nat::tail_addmul(Nat::tail_add(m, r), n0, m);
  }
}

__attribute__((pure)) unsigned int Nat::tail_mul(const unsigned int n,
                                                 const unsigned int m) {
  return Nat::tail_addmul(0u, n, m);
}

__attribute__((pure)) unsigned int
Nat::of_uint_acc(const std::shared_ptr<Uint> &d, const unsigned int acc) {
  return std::visit(
      Overloaded{
          [&](const typename Uint::Nil _args) -> unsigned int {
            return std::move(acc);
          },
          [&](const typename Uint::D0 _args) -> unsigned int {
            return Nat::of_uint_acc(_args.d_a0,
                                    Nat::tail_mul(10u, std::move(acc)));
          },
          [&](const typename Uint::D1 _args) -> unsigned int {
            return Nat::of_uint_acc(_args.d_a0,
                                    (Nat::tail_mul(10u, std::move(acc)) + 1));
          },
          [&](const typename Uint::D2 _args) -> unsigned int {
            return Nat::of_uint_acc(
                _args.d_a0, ((Nat::tail_mul(10u, std::move(acc)) + 1) + 1));
          },
          [&](const typename Uint::D3 _args) -> unsigned int {
            return Nat::of_uint_acc(
                _args.d_a0,
                (((Nat::tail_mul(10u, std::move(acc)) + 1) + 1) + 1));
          },
          [&](const typename Uint::D4 _args) -> unsigned int {
            return Nat::of_uint_acc(
                _args.d_a0,
                ((((Nat::tail_mul(10u, std::move(acc)) + 1) + 1) + 1) + 1));
          },
          [&](const typename Uint::D5 _args) -> unsigned int {
            return Nat::of_uint_acc(
                _args.d_a0,
                (((((Nat::tail_mul(10u, std::move(acc)) + 1) + 1) + 1) + 1) +
                 1));
          },
          [&](const typename Uint::D6 _args) -> unsigned int {
            return Nat::of_uint_acc(
                _args.d_a0,
                ((((((Nat::tail_mul(10u, std::move(acc)) + 1) + 1) + 1) + 1) +
                  1) +
                 1));
          },
          [&](const typename Uint::D7 _args) -> unsigned int {
            return Nat::of_uint_acc(
                _args.d_a0,
                (((((((Nat::tail_mul(10u, std::move(acc)) + 1) + 1) + 1) + 1) +
                   1) +
                  1) +
                 1));
          },
          [&](const typename Uint::D8 _args) -> unsigned int {
            return Nat::of_uint_acc(
                _args.d_a0,
                ((((((((Nat::tail_mul(10u, std::move(acc)) + 1) + 1) + 1) + 1) +
                    1) +
                   1) +
                  1) +
                 1));
          },
          [&](const typename Uint::D9 _args) -> unsigned int {
            return Nat::of_uint_acc(
                _args.d_a0,
                (((((((((Nat::tail_mul(10u, std::move(acc)) + 1) + 1) + 1) +
                      1) +
                     1) +
                    1) +
                   1) +
                  1) +
                 1));
          }},
      d->v());
}

__attribute__((pure)) unsigned int
Nat::of_uint(const std::shared_ptr<Uint> &d) {
  return Nat::of_uint_acc(d, 0u);
}

__attribute__((pure)) unsigned int
Nat::of_hex_uint_acc(const std::shared_ptr<Uint0> &d, const unsigned int acc) {
  return std::visit(
      Overloaded{
          [&](const typename Uint0::Nil0 _args) -> unsigned int {
            return std::move(acc);
          },
          [&](const typename Uint0::D10 _args) -> unsigned int {
            return Nat::of_hex_uint_acc(_args.d_a0,
                                        Nat::tail_mul(16u, std::move(acc)));
          },
          [&](const typename Uint0::D11 _args) -> unsigned int {
            return Nat::of_hex_uint_acc(
                _args.d_a0, (Nat::tail_mul(16u, std::move(acc)) + 1));
          },
          [&](const typename Uint0::D12 _args) -> unsigned int {
            return Nat::of_hex_uint_acc(
                _args.d_a0, ((Nat::tail_mul(16u, std::move(acc)) + 1) + 1));
          },
          [&](const typename Uint0::D13 _args) -> unsigned int {
            return Nat::of_hex_uint_acc(
                _args.d_a0,
                (((Nat::tail_mul(16u, std::move(acc)) + 1) + 1) + 1));
          },
          [&](const typename Uint0::D14 _args) -> unsigned int {
            return Nat::of_hex_uint_acc(
                _args.d_a0,
                ((((Nat::tail_mul(16u, std::move(acc)) + 1) + 1) + 1) + 1));
          },
          [&](const typename Uint0::D15 _args) -> unsigned int {
            return Nat::of_hex_uint_acc(
                _args.d_a0,
                (((((Nat::tail_mul(16u, std::move(acc)) + 1) + 1) + 1) + 1) +
                 1));
          },
          [&](const typename Uint0::D16 _args) -> unsigned int {
            return Nat::of_hex_uint_acc(
                _args.d_a0,
                ((((((Nat::tail_mul(16u, std::move(acc)) + 1) + 1) + 1) + 1) +
                  1) +
                 1));
          },
          [&](const typename Uint0::D17 _args) -> unsigned int {
            return Nat::of_hex_uint_acc(
                _args.d_a0,
                (((((((Nat::tail_mul(16u, std::move(acc)) + 1) + 1) + 1) + 1) +
                   1) +
                  1) +
                 1));
          },
          [&](const typename Uint0::D18 _args) -> unsigned int {
            return Nat::of_hex_uint_acc(
                _args.d_a0,
                ((((((((Nat::tail_mul(16u, std::move(acc)) + 1) + 1) + 1) + 1) +
                    1) +
                   1) +
                  1) +
                 1));
          },
          [&](const typename Uint0::D19 _args) -> unsigned int {
            return Nat::of_hex_uint_acc(
                _args.d_a0,
                (((((((((Nat::tail_mul(16u, std::move(acc)) + 1) + 1) + 1) +
                      1) +
                     1) +
                    1) +
                   1) +
                  1) +
                 1));
          },
          [&](const typename Uint0::Da _args) -> unsigned int {
            return Nat::of_hex_uint_acc(
                _args.d_a0,
                ((((((((((Nat::tail_mul(16u, std::move(acc)) + 1) + 1) + 1) +
                       1) +
                      1) +
                     1) +
                    1) +
                   1) +
                  1) +
                 1));
          },
          [&](const typename Uint0::Db _args) -> unsigned int {
            return Nat::of_hex_uint_acc(
                _args.d_a0,
                (((((((((((Nat::tail_mul(16u, std::move(acc)) + 1) + 1) + 1) +
                        1) +
                       1) +
                      1) +
                     1) +
                    1) +
                   1) +
                  1) +
                 1));
          },
          [&](const typename Uint0::Dc _args) -> unsigned int {
            return Nat::of_hex_uint_acc(
                _args.d_a0,
                ((((((((((((Nat::tail_mul(16u, std::move(acc)) + 1) + 1) + 1) +
                         1) +
                        1) +
                       1) +
                      1) +
                     1) +
                    1) +
                   1) +
                  1) +
                 1));
          },
          [&](const typename Uint0::Dd _args) -> unsigned int {
            return Nat::of_hex_uint_acc(
                _args.d_a0,
                (((((((((((((Nat::tail_mul(16u, std::move(acc)) + 1) + 1) + 1) +
                          1) +
                         1) +
                        1) +
                       1) +
                      1) +
                     1) +
                    1) +
                   1) +
                  1) +
                 1));
          },
          [&](const typename Uint0::De _args) -> unsigned int {
            return Nat::of_hex_uint_acc(
                _args.d_a0,
                ((((((((((((((Nat::tail_mul(16u, std::move(acc)) + 1) + 1) +
                            1) +
                           1) +
                          1) +
                         1) +
                        1) +
                       1) +
                      1) +
                     1) +
                    1) +
                   1) +
                  1) +
                 1));
          },
          [&](const typename Uint0::Df _args) -> unsigned int {
            return Nat::of_hex_uint_acc(
                _args.d_a0,
                (((((((((((((((Nat::tail_mul(16u, std::move(acc)) + 1) + 1) +
                             1) +
                            1) +
                           1) +
                          1) +
                         1) +
                        1) +
                       1) +
                      1) +
                     1) +
                    1) +
                   1) +
                  1) +
                 1));
          }},
      d->v());
}

__attribute__((pure)) unsigned int
Nat::of_hex_uint(const std::shared_ptr<Uint0> &d) {
  return Nat::of_hex_uint_acc(d, 0u);
}

__attribute__((pure)) unsigned int
Nat::of_num_uint(const std::shared_ptr<Uint1> &d) {
  return std::visit(
      Overloaded{[](const typename Uint1::UIntDecimal _args) -> unsigned int {
                   return Nat::of_uint(_args.d_u);
                 },
                 [](const typename Uint1::UIntHexadecimal _args)
                     -> unsigned int { return Nat::of_hex_uint(_args.d_u); }},
      d->v());
}
