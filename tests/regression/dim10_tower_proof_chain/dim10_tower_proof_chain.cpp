#include "dim10_tower_proof_chain.h"

Dim10TowerProofChainCase::nat_le
Dim10TowerProofChainCase::nat_le_of_lt(uint64_t n, uint64_t m, std::any _H) {
  if (n <= 0) {
    if (m <= 0) {
      return std::monostate{};
    } else {
      uint64_t _x = m - 1;
      return std::monostate{};
    }
  } else {
    uint64_t n0 = n - 1;
    if (m <= 0) {
      throw std::logic_error("absurd case");
    } else {
      uint64_t n1 = m - 1;
      return nat_le_of_lt(n0, n1, _H);
    }
  }
}

uint64_t
Dim10TowerProofChainCase::qpos_denom(const Dim10TowerProofChainCase::QPos &q) {
  return (q.qpos_denom_pred + 1);
}

Dim10TowerProofChainCase::QPos
Dim10TowerProofChainCase::nat_to_qpos(uint64_t n) {
  return QPos{n, UINT64_C(0)};
}

uint64_t Dim10TowerProofChainCase::nat_sub(uint64_t n, uint64_t m) {
  if (n <= 0) {
    return UINT64_C(0);
  } else {
    uint64_t n_ = n - 1;
    if (m <= 0) {
      return (n_ + 1);
    } else {
      uint64_t m_ = m - 1;
      return nat_sub(n_, m_);
    }
  }
}

uint64_t Dim10TowerProofChainCase::poly_approx_dim(uint64_t _x0, uint64_t _x1) {
  return nat_sub(_x0, _x1);
}

uint64_t Dim10TowerProofChainCase::layer_dim(uint64_t base_dim, uint64_t n) {
  return nat_sub(poly_approx_dim(base_dim, n),
                 poly_approx_dim(base_dim, (n + 1)));
}

Dim10TowerProofChainCase::GradedObj
Dim10TowerProofChainCase::layer_obj(uint64_t base_dim, uint64_t n) {
  return GradedObj{layer_dim(base_dim, n)};
}

Dim10TowerProofChainCase::QPos
Dim10TowerProofChainCase::layer_measure(uint64_t base_dim, uint64_t n) {
  return nat_to_qpos(layer_dim(base_dim, n));
}

Dim10TowerProofChainCase::EventuallyZero
Dim10TowerProofChainCase::layer_measure_eventually_zero(uint64_t base_dim) {
  return SigT<uint64_t, std::any>::existt(base_dim, std::any{});
}

Dim10TowerProofChainCase::GradedObj Dim10TowerProofChainCase::P_n_obj(
    uint64_t n, const Dim10TowerProofChainCase::GradedObj &x) {
  return GradedObj{poly_approx_dim(x.go_dim, n)};
}

Dim10TowerProofChainCase::GradedObj
Dim10TowerProofChainCase::D_n_obj(uint64_t _x0, uint64_t _x1) {
  return layer_obj(_x0, _x1);
}

Dim10TowerProofChainCase::QPos
Dim10TowerProofChainCase::D_n_measure(uint64_t _x0, uint64_t _x1) {
  return layer_measure(_x0, _x1);
}

Dim10TowerProofChainCase::EventuallyZero
Dim10TowerProofChainCase::D_n_measure_eventually_zero(uint64_t _x0) {
  return layer_measure_eventually_zero(_x0);
}

Dim10TowerProofChainCase::GradedGoodwillieTower
Dim10TowerProofChainCase::make_graded_goodwillie_tower(uint64_t base_dim) {
  return GradedGoodwillieTower{
      [=](uint64_t n) mutable { return P_n_obj(n, GradedObj{base_dim}); },
      [=](uint64_t n) mutable { return D_n_obj(base_dim, n); }};
}

SigT<uint64_t, std::any>
Dim10TowerProofChainCase::graded_goodwillie_layers_stabilize(
    uint64_t base_dim) {
  SigT<uint64_t, std::any> e = D_n_measure_eventually_zero(base_dim);
  auto &[x0, a1] = e;
  return SigT<uint64_t, std::any>::existt(std::move(x0), std::any{});
}

SigT<uint64_t, std::any>
Dim10TowerProofChainCase::graded_goodwillie_P_stabilizes(uint64_t base_dim) {
  return SigT<uint64_t, std::any>::existt(base_dim, std::any{});
}

std::pair<std::pair<std::pair<Dim10TowerProofChainCase::IsIntegerValued,
                              Dim10TowerProofChainCase::EventuallyZero>,
                    SigT<uint64_t, std::any>>,
          SigT<uint64_t, std::any>>
Dim10TowerProofChainCase::graded_complete_proof_chain(uint64_t base_dim) {
  return std::make_pair(
      std::make_pair(
          std::make_pair(std::any{}, D_n_measure_eventually_zero(base_dim)),
          graded_goodwillie_layers_stabilize(base_dim)),
      graded_goodwillie_P_stabilizes(base_dim));
}

Dim10TowerProofChainCase::GoodwillieProofChain
Dim10TowerProofChainCase::make_goodwillie_proof_chain(uint64_t base_dim) {
  return GoodwillieProofChain{D_n_measure_eventually_zero(base_dim),
                              graded_goodwillie_layers_stabilize(base_dim),
                              graded_goodwillie_P_stabilizes(base_dim)};
}
