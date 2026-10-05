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
    requires crane_convertible<CraneU0, const A &> &&
             crane_convertible<CraneU1, const P &>
  operator SigT<CraneU0, CraneU1>() const {
    return {crane_convert<CraneU0>(x), crane_convert<CraneU1>(a1)};
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
  static constexpr uint64_t dim10_p0_dim = UINT64_C(10);
  static constexpr uint64_t dim10_p4_dim = UINT64_C(6);
  static constexpr uint64_t dim10_p9_dim = UINT64_C(1);
  static constexpr uint64_t dim10_p10_dim = UINT64_C(0);
  static constexpr uint64_t dim10_p12_dim = UINT64_C(0);
  static constexpr uint64_t dim10_d0_dim = UINT64_C(1);
  static constexpr uint64_t dim10_d4_dim = UINT64_C(1);
  static constexpr uint64_t dim10_d9_dim = UINT64_C(1);
  static constexpr uint64_t dim10_d10_dim = UINT64_C(0);
  static constexpr uint64_t dim10_layers_cutoff = UINT64_C(10);
  static constexpr uint64_t dim10_P_cutoff = UINT64_C(10);
  static constexpr bool dim10_layers_cutoff_matches = true;
  static constexpr bool dim10_P_cutoff_matches = true;
  static constexpr uint64_t dim10_dimension_checksum = UINT64_C(40);
};

#endif // INCLUDED_DIM10_TOWER_PROOF_CHAIN
