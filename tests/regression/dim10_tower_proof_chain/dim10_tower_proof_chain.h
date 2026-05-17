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
  static nat_le nat_le_of_lt(unsigned int n, unsigned int m, std::any _H);

  struct QPos {
    unsigned int qpos_num;
    unsigned int qpos_denom_pred;

    // ACCESSORS
    QPos clone() const {
      return QPos{(*this).qpos_num, (*this).qpos_denom_pred};
    }
  };

  static unsigned int qpos_denom(const QPos &q);
  static QPos nat_to_qpos(unsigned int n);
  using EventuallyZero = SigT<unsigned int, std::any>;
  using IsIntegerValued = std::any;

  struct GradedObj {
    unsigned int go_dim;

    // ACCESSORS
    GradedObj clone() const { return GradedObj{(*this).go_dim}; }
  };

  static inline const GradedObj go_zero = GradedObj{0u};
  static unsigned int nat_sub(unsigned int n, unsigned int m);
  static unsigned int poly_approx_dim(unsigned int _x0, unsigned int _x1);
  static unsigned int layer_dim(unsigned int base_dim, unsigned int n);
  static GradedObj layer_obj(unsigned int base_dim, unsigned int n);
  static QPos layer_measure(unsigned int base_dim, unsigned int n);
  static EventuallyZero layer_measure_eventually_zero(unsigned int base_dim);
  static GradedObj P_n_obj(unsigned int n, const GradedObj &x);
  static GradedObj D_n_obj(unsigned int _x0, unsigned int _x1);
  static QPos D_n_measure(unsigned int _x0, unsigned int _x1);
  static EventuallyZero D_n_measure_eventually_zero(unsigned int _x0);

  struct GradedGoodwillieTower {
    std::function<GradedObj(unsigned int)> ggt_P;
    std::function<GradedObj(unsigned int)> ggt_D;

    // ACCESSORS
    GradedGoodwillieTower clone() const {
      return GradedGoodwillieTower{(*this).ggt_P, (*this).ggt_D};
    }
  };

  static GradedGoodwillieTower
  make_graded_goodwillie_tower(unsigned int base_dim);
  static SigT<unsigned int, std::any>
  graded_goodwillie_layers_stabilize(unsigned int base_dim);
  static SigT<unsigned int, std::any>
  graded_goodwillie_P_stabilizes(unsigned int base_dim);
  static inline const GradedGoodwillieTower dim10_tower =
      make_graded_goodwillie_tower(10u);
  static inline const SigT<unsigned int, std::any> dim10_layers_stabilize =
      []() {
        SigT<unsigned int, std::any> s =
            graded_goodwillie_layers_stabilize(10u);
        auto &[x0, a1] = s;
        return SigT<unsigned int, std::any>::existt(std::move(x0), std::any{});
      }();
  static inline const SigT<unsigned int, std::any> dim10_P_stabilizes = []() {
    SigT<unsigned int, std::any> s = graded_goodwillie_P_stabilizes(10u);
    auto &[x0, a1] = s;
    return SigT<unsigned int, std::any>::existt(std::move(x0), std::any{});
  }();
  static std::pair<std::pair<std::pair<IsIntegerValued, EventuallyZero>,
                             SigT<unsigned int, std::any>>,
                   SigT<unsigned int, std::any>>
  graded_complete_proof_chain(unsigned int base_dim);

  struct GoodwillieProofChain {
    EventuallyZero gc_eventually_zero;
    SigT<unsigned int, std::any> gc_layers_stabilize;
    SigT<unsigned int, std::any> gc_P_stabilize;

    // ACCESSORS
    GoodwillieProofChain clone() const {
      return GoodwillieProofChain{(*this).gc_eventually_zero,
                                  (*this).gc_layers_stabilize.clone(),
                                  (*this).gc_P_stabilize.clone()};
    }
  };

  static GoodwillieProofChain
  make_goodwillie_proof_chain(unsigned int base_dim);
  static inline const GoodwillieProofChain dim10_chain =
      make_goodwillie_proof_chain(10u);
  static inline const std::pair<
      std::pair<std::pair<IsIntegerValued, EventuallyZero>,
                SigT<unsigned int, std::any>>,
      SigT<unsigned int, std::any>>
      dim10_pair_chain = graded_complete_proof_chain(10u);

  struct Dim10Bundle {
    GradedGoodwillieTower dt_tower;
    GoodwillieProofChain dt_chain;

    // ACCESSORS
    Dim10Bundle clone() const {
      return Dim10Bundle{(*this).dt_tower.clone(), (*this).dt_chain.clone()};
    }
  };

  static inline const Dim10Bundle dim10_bundle =
      Dim10Bundle{dim10_tower, dim10_chain};
  static inline const unsigned int dim10_p0_dim =
      dim10_bundle.dt_tower.ggt_P(0u).go_dim;
  static inline const unsigned int dim10_p4_dim =
      dim10_bundle.dt_tower.ggt_P(4u).go_dim;
  static inline const unsigned int dim10_p9_dim =
      dim10_bundle.dt_tower.ggt_P(9u).go_dim;
  static inline const unsigned int dim10_p10_dim =
      dim10_bundle.dt_tower.ggt_P(10u).go_dim;
  static inline const unsigned int dim10_p12_dim =
      dim10_bundle.dt_tower.ggt_P(12u).go_dim;
  static inline const unsigned int dim10_d0_dim =
      dim10_bundle.dt_tower.ggt_D(0u).go_dim;
  static inline const unsigned int dim10_d4_dim =
      dim10_bundle.dt_tower.ggt_D(4u).go_dim;
  static inline const unsigned int dim10_d9_dim =
      dim10_bundle.dt_tower.ggt_D(9u).go_dim;
  static inline const unsigned int dim10_d10_dim =
      dim10_bundle.dt_tower.ggt_D(10u).go_dim;
  static inline const unsigned int dim10_layers_cutoff = []() {
    const auto &_sv = dim10_bundle.dt_chain.gc_layers_stabilize;
    const auto &[x, a1] = _sv;
    return x;
  }();
  static inline const unsigned int dim10_P_cutoff = []() {
    const auto &_sv0 = dim10_bundle.dt_chain.gc_P_stabilize;
    const auto &[x0, a10] = _sv0;
    return x0;
  }();
  static inline const bool dim10_layers_cutoff_matches =
      dim10_layers_cutoff == 10u;
  static inline const bool dim10_P_cutoff_matches = dim10_P_cutoff == 10u;
  static inline const unsigned int dim10_dimension_checksum =
      (((((((((dim10_p0_dim + dim10_p4_dim) + dim10_p9_dim) + dim10_p10_dim) +
            dim10_d0_dim) +
           dim10_d4_dim) +
          dim10_d9_dim) +
         dim10_d10_dim) +
        dim10_layers_cutoff) +
       dim10_P_cutoff);
};

#endif // INCLUDED_DIM10_TOWER_PROOF_CHAIN
