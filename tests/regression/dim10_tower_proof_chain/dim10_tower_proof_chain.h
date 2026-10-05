#ifndef INCLUDED_DIM10_TOWER_PROOF_CHAIN
#define INCLUDED_DIM10_TOWER_PROOF_CHAIN

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include <cstdint>
#include <stdexcept>
#include <utility>
#include <variant>

template <typename A, typename P> struct SigT;

template <typename A, typename P> struct SigT {
  // DATA
  A x;
  P a1;

  // ACCESSORS
  SigT<A, P> clone() const { return {x, a1}; }

  template <typename CraneU0, typename CraneU1>
  operator SigT<CraneU0, CraneU1>() const {
    return {[&]() -> CraneU0 {
              if constexpr (crane_convertible<CraneU0, const A &>) {
                return crane_convert<CraneU0>(x);
              } else {
                throw std::logic_error("unreachable: inactive constructor "
                                       "field at this instantiation");
              }
            }(),
            [&]() -> CraneU1 {
              if constexpr (crane_convertible<CraneU1, const P &>) {
                return crane_convert<CraneU1>(a1);
              } else {
                throw std::logic_error("unreachable: inactive constructor "
                                       "field at this instantiation");
              }
            }()};
  }

  // CREATORS
  static SigT<A, P> existt(A x, P a1) { return {std::move(x), std::move(a1)}; }
};

struct Dim10TowerProofChainCase {
  using nat_lt = crane::obj;
  using nat_le = crane::obj;
  static nat_le nat_le_of_lt(uint64_t n, uint64_t m, nat_lt h_);

  struct QPos {
    uint64_t qpos_num;
    uint64_t qpos_denom_pred;
  };

  static uint64_t qpos_denom(const QPos &q);
  static QPos nat_to_qpos(uint64_t n);
  using EventuallyZero = SigT<uint64_t, crane::obj>;
  using IsIntegerValued = crane::obj;

  struct GradedObj {
    uint64_t go_dim;
  };

  static inline const GradedObj go_zero = GradedObj{UINT64_C(0)};
  static uint64_t nat_sub(uint64_t n, uint64_t m);
  static uint64_t poly_approx_dim(uint64_t x0_, uint64_t x1_);
  static uint64_t layer_dim(uint64_t base_dim, uint64_t n);
  static GradedObj layer_obj(uint64_t base_dim, uint64_t n);
  static QPos layer_measure(uint64_t base_dim, uint64_t n);
  static EventuallyZero layer_measure_eventually_zero(uint64_t base_dim);
  static GradedObj P_n_obj(uint64_t n, const GradedObj &x);
  static GradedObj D_n_obj(uint64_t x0_, uint64_t x1_);
  static QPos D_n_measure(uint64_t x0_, uint64_t x1_);
  static EventuallyZero D_n_measure_eventually_zero(uint64_t x0_);

  struct GradedGoodwillieTower {
    crane::fn<GradedObj(uint64_t)> ggt_P;
    crane::fn<GradedObj(uint64_t)> ggt_D;
  };

  static GradedGoodwillieTower make_graded_goodwillie_tower(uint64_t base_dim);
  static SigT<uint64_t, crane::obj>
  graded_goodwillie_layers_stabilize(uint64_t base_dim);
  static SigT<uint64_t, crane::obj>
  graded_goodwillie_P_stabilizes(uint64_t base_dim);
  static inline const GradedGoodwillieTower dim10_tower =
      make_graded_goodwillie_tower(UINT64_C(10));
  static inline const SigT<uint64_t, crane::obj> dim10_layers_stabilize = []() {
    auto s = graded_goodwillie_layers_stabilize(UINT64_C(10));
    auto &[x0, a1] = s;
    return SigT<uint64_t, crane::obj>::existt(std::move(x0), crane::obj());
  }();
  static inline const SigT<uint64_t, crane::obj> dim10_P_stabilizes = []() {
    auto s = graded_goodwillie_P_stabilizes(UINT64_C(10));
    auto &[x0, a1] = s;
    return SigT<uint64_t, crane::obj>::existt(std::move(x0), crane::obj());
  }();
  static std::pair<std::pair<std::pair<IsIntegerValued, EventuallyZero>,
                             SigT<uint64_t, crane::obj>>,
                   SigT<uint64_t, crane::obj>>
  graded_complete_proof_chain(uint64_t base_dim);

  struct GoodwillieProofChain {
    EventuallyZero gc_eventually_zero;
    SigT<uint64_t, crane::obj> gc_layers_stabilize;
    SigT<uint64_t, crane::obj> gc_P_stabilize;
  };

  static GoodwillieProofChain make_goodwillie_proof_chain(uint64_t base_dim);
  static inline const GoodwillieProofChain dim10_chain =
      make_goodwillie_proof_chain(UINT64_C(10));
  static inline const std::pair<
      std::pair<std::pair<IsIntegerValued, EventuallyZero>,
                SigT<uint64_t, crane::obj>>,
      SigT<uint64_t, crane::obj>>
      dim10_pair_chain = graded_complete_proof_chain(UINT64_C(10));

  struct Dim10Bundle {
    GradedGoodwillieTower dt_tower;
    GoodwillieProofChain dt_chain;
  };

  static inline const Dim10Bundle dim10_bundle =
      Dim10Bundle{dim10_tower, dim10_chain};
  static inline const uint64_t dim10_p0_dim =
      dim10_bundle.dt_tower.ggt_P(UINT64_C(0)).go_dim;
  static inline const uint64_t dim10_p4_dim =
      dim10_bundle.dt_tower.ggt_P(UINT64_C(4)).go_dim;
  static inline const uint64_t dim10_p9_dim =
      dim10_bundle.dt_tower.ggt_P(UINT64_C(9)).go_dim;
  static inline const uint64_t dim10_p10_dim =
      dim10_bundle.dt_tower.ggt_P(UINT64_C(10)).go_dim;
  static inline const uint64_t dim10_p12_dim =
      dim10_bundle.dt_tower.ggt_P(UINT64_C(12)).go_dim;
  static inline const uint64_t dim10_d0_dim =
      dim10_bundle.dt_tower.ggt_D(UINT64_C(0)).go_dim;
  static inline const uint64_t dim10_d4_dim =
      dim10_bundle.dt_tower.ggt_D(UINT64_C(4)).go_dim;
  static inline const uint64_t dim10_d9_dim =
      dim10_bundle.dt_tower.ggt_D(UINT64_C(9)).go_dim;
  static inline const uint64_t dim10_d10_dim =
      dim10_bundle.dt_tower.ggt_D(UINT64_C(10)).go_dim;
  static inline const uint64_t dim10_layers_cutoff = []() {
    const auto &_sv = dim10_bundle.dt_chain.gc_layers_stabilize;
    const auto &[x, a1] = _sv;
    return x;
  }();
  static inline const uint64_t dim10_P_cutoff = []() {
    const auto &_sv = dim10_bundle.dt_chain.gc_P_stabilize;
    const auto &[x, a1] = _sv;
    return x;
  }();
  static inline const bool dim10_layers_cutoff_matches =
      dim10_layers_cutoff == UINT64_C(10);
  static inline const bool dim10_P_cutoff_matches =
      dim10_P_cutoff == UINT64_C(10);
  static inline const uint64_t dim10_dimension_checksum =
      (((((((((dim10_p0_dim + dim10_p4_dim) + dim10_p9_dim) + dim10_p10_dim) +
            dim10_d0_dim) +
           dim10_d4_dim) +
          dim10_d9_dim) +
         dim10_d10_dim) +
        dim10_layers_cutoff) +
       dim10_P_cutoff);
};

#endif // INCLUDED_DIM10_TOWER_PROOF_CHAIN
