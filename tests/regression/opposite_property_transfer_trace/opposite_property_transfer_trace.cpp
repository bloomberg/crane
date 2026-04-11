#include <opposite_property_transfer_trace.h>

#include <functional>
#include <memory>
#include <type_traits>
#include <utility>

std::shared_ptr<OppositePropertyTransferTraceCase::PreStableCategory>
OppositePropertyTransferTraceCase::opposite_prestable_category(
    std::shared_ptr<OppositePropertyTransferTraceCase::PreStableCategory> pS) {
  return std::make_shared<OppositePropertyTransferTraceCase::PreStableCategory>(
      PreStableCategory{pS->ps_tag, pS->ps_shift, pS->ps_Loop, pS->ps_Susp,
                        pS->ps_epsilon, pS->ps_eta});
}

__attribute__((pure)) OppositePropertyTransferTraceCase::is_left_semi_stable
OppositePropertyTransferTraceCase::right_stable_gives_opposite_left(
    const std::shared_ptr<OppositePropertyTransferTraceCase::PreStableCategory>
        &,
    const std::shared_ptr<OppositePropertyTransferTraceCase::RightStableWitness>
        &h) {
  unsigned int rsw_seed0 = h->rsw_seed;
  unsigned int rsw_value0 = h->rsw_value;
  return std::make_shared<OppositePropertyTransferTraceCase::LeftStableWitness>(
      LeftStableWitness{rsw_seed0, rsw_value0});
}

__attribute__((pure)) OppositePropertyTransferTraceCase::EquivT<
    OppositePropertyTransferTraceCase::satisfies_triangle_1,
    OppositePropertyTransferTraceCase::satisfies_triangle_2>
OppositePropertyTransferTraceCase::triangle_identity_duality(
    const std::shared_ptr<OppositePropertyTransferTraceCase::PreStableCategory>
        &) {
  return std::make_pair(
      [](std::shared_ptr<OppositePropertyTransferTraceCase::Triangle1Witness>
             h) {
        unsigned int t1_seed0 = h->t1_seed;
        unsigned int t1_value0 = h->t1_value;
        return std::make_shared<
            OppositePropertyTransferTraceCase::Triangle2Witness>(
            Triangle2Witness{t1_seed0, t1_value0});
      },
      [](std::shared_ptr<OppositePropertyTransferTraceCase::Triangle2Witness>
             h) {
        unsigned int t2_seed0 = h->t2_seed;
        unsigned int t2_value0 = h->t2_value;
        return std::make_shared<
            OppositePropertyTransferTraceCase::Triangle1Witness>(
            Triangle1Witness{t2_seed0, t2_value0});
      });
}

std::shared_ptr<OppositePropertyTransferTraceCase::LeftProperty>
OppositePropertyTransferTraceCase::sample_left_property(
    std::shared_ptr<OppositePropertyTransferTraceCase::PreStableCategory> pS,
    const std::shared_ptr<OppositePropertyTransferTraceCase::LeftStableWitness>
        &h_left,
    const std::shared_ptr<OppositePropertyTransferTraceCase::Triangle1Witness>
        &) {
  unsigned int lsw_seed0 = h_left->lsw_seed;
  unsigned int lsw_value0 = h_left->lsw_value;
  return std::make_shared<OppositePropertyTransferTraceCase::LeftProperty>(
      LeftProperty{lsw_seed0, ((lsw_value0 + pS->ps_shift) + pS->ps_tag),
                   pS->ps_tag});
}

__attribute__((pure)) OppositePropertyTransferTraceCase::EquivT<
    std::shared_ptr<OppositePropertyTransferTraceCase::LeftProperty>,
    std::shared_ptr<OppositePropertyTransferTraceCase::RightProperty>>
OppositePropertyTransferTraceCase::dual_property_equiv(
    const std::shared_ptr<OppositePropertyTransferTraceCase::PreStableCategory>
        &) {
  return std::make_pair(
      [](std::shared_ptr<OppositePropertyTransferTraceCase::LeftProperty> h) {
        unsigned int lp_seed0 = h->lp_seed;
        unsigned int lp_value0 = h->lp_value;
        unsigned int lp_tag0 = h->lp_tag;
        return std::make_shared<
            OppositePropertyTransferTraceCase::RightProperty>(
            RightProperty{lp_seed0, lp_value0, lp_tag0});
      },
      [](std::shared_ptr<OppositePropertyTransferTraceCase::RightProperty> h) {
        unsigned int rp_seed0 = h->rp_seed;
        unsigned int rp_value0 = h->rp_value;
        unsigned int rp_tag0 = h->rp_tag;
        return std::make_shared<
            OppositePropertyTransferTraceCase::LeftProperty>(
            LeftProperty{rp_seed0, rp_value0, rp_tag0});
      });
}
