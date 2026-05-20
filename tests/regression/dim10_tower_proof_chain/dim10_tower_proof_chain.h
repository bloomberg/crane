#ifndef INCLUDED_DIM10_TOWER_PROOF_CHAIN
#define INCLUDED_DIM10_TOWER_PROOF_CHAIN

#include <any>
#include <functional>
#include <stdexcept>
#include <utility>
#include <variant>

template <typename A, typename P> struct SigT {
  // DATA
  A x;
  P a1;

  // ACCESSORS
  SigT<A, P> clone() const { return {x, a1}; }

  // CREATORS
  static SigT<A, P> existt(A x, P a1) { return {std::move(x), std::move(a1)}; }
};

struct Dim10TowerProofChainCase {
  using nat_lt = std::any;
  using nat_le = std::any;
  static nat_le nat_le_of_lt(uint64_t n, uint64_t m, std::any _H);

  struct QPos {
    uint64_t qpos_num;
    uint64_t qpos_denom_pred;

    // ACCESSORS
    QPos clone() const { return QPos{this->qpos_num, this->qpos_denom_pred}; }
  };

  static uint64_t qpos_denom(const QPos &q);
  static QPos nat_to_qpos(uint64_t n);
  using EventuallyZero = SigT<uint64_t, std::any>;
  using IsIntegerValued = std::any;

  struct GradedObj {
    uint64_t go_dim;

    // ACCESSORS
    GradedObj clone() const { return GradedObj{this->go_dim}; }
  };

  static inline const GradedObj go_zero = GradedObj{UINT64_C(0)};
  static uint64_t nat_sub(uint64_t n, uint64_t m);
  static uint64_t poly_approx_dim(uint64_t _x0, uint64_t _x1);
  static uint64_t layer_dim(uint64_t base_dim, uint64_t n);
  static GradedObj layer_obj(uint64_t base_dim, uint64_t n);
  static QPos layer_measure(uint64_t base_dim, uint64_t n);
  static EventuallyZero layer_measure_eventually_zero(uint64_t base_dim);
  static GradedObj P_n_obj(uint64_t n, const GradedObj &x);
  static GradedObj D_n_obj(uint64_t _x0, uint64_t _x1);
  static QPos D_n_measure(uint64_t _x0, uint64_t _x1);
  static EventuallyZero D_n_measure_eventually_zero(uint64_t _x0);

  struct GradedGoodwillieTower {
    std::function<GradedObj(uint64_t)> ggt_P;
    std::function<GradedObj(uint64_t)> ggt_D;

    // ACCESSORS
    GradedGoodwillieTower clone() const {
      return GradedGoodwillieTower{this->ggt_P, this->ggt_D};
    }
  };

  static GradedGoodwillieTower make_graded_goodwillie_tower(uint64_t base_dim);
  static SigT<uint64_t, std::any>
  graded_goodwillie_layers_stabilize(uint64_t base_dim);
  static SigT<uint64_t, std::any>
  graded_goodwillie_P_stabilizes(uint64_t base_dim);
  static inline const GradedGoodwillieTower dim10_tower =
      make_graded_goodwillie_tower(UINT64_C(10));
  static inline const SigT<uint64_t, std::any> dim10_layers_stabilize = []() {
    SigT<uint64_t, std::any> s =
        graded_goodwillie_layers_stabilize(UINT64_C(10));
    auto &[x0, a1] = s;
    return SigT<uint64_t, std::any>::existt(std::move(x0), std::any{});
  }();
  static inline const SigT<uint64_t, std::any> dim10_P_stabilizes = []() {
    SigT<uint64_t, std::any> s = graded_goodwillie_P_stabilizes(UINT64_C(10));
    auto &[x0, a1] = s;
    return SigT<uint64_t, std::any>::existt(std::move(x0), std::any{});
  }();
  static std::pair<std::pair<std::pair<IsIntegerValued, EventuallyZero>,
                             SigT<uint64_t, std::any>>,
                   SigT<uint64_t, std::any>>
  graded_complete_proof_chain(uint64_t base_dim);

  struct GoodwillieProofChain {
    EventuallyZero gc_eventually_zero;
    SigT<uint64_t, std::any> gc_layers_stabilize;
    SigT<uint64_t, std::any> gc_P_stabilize;

    // ACCESSORS
    GoodwillieProofChain clone() const {
      return GoodwillieProofChain{this->gc_eventually_zero,
                                  this->gc_layers_stabilize.clone(),
                                  this->gc_P_stabilize.clone()};
    }
  };

  static GoodwillieProofChain make_goodwillie_proof_chain(uint64_t base_dim);
  static inline const GoodwillieProofChain dim10_chain =
      make_goodwillie_proof_chain(UINT64_C(10));
  static inline const std::pair<
      std::pair<std::pair<IsIntegerValued, EventuallyZero>,
                SigT<uint64_t, std::any>>,
      SigT<uint64_t, std::any>>
      dim10_pair_chain = graded_complete_proof_chain(UINT64_C(10));

  struct Dim10Bundle {
    GradedGoodwillieTower dt_tower;
    GoodwillieProofChain dt_chain;

    // ACCESSORS
    Dim10Bundle clone() const {
      return Dim10Bundle{this->dt_tower.clone(), this->dt_chain.clone()};
    }
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
    const auto &_sv0 = dim10_bundle.dt_chain.gc_P_stabilize;
    const auto &[x0, a10] = _sv0;
    return x0;
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
