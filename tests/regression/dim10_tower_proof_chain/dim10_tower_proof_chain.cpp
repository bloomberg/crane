#include "dim10_tower_proof_chain.h"

Dim10TowerProofChainCase::nat_le
Dim10TowerProofChainCase::nat_le_of_lt(unsigned int n, unsigned int m,
                                       std::any _H) {
  if (n <= 0) {
    if (m <= 0) {
      return std::monostate{};
    } else {
      unsigned int _x = m - 1;
      return std::monostate{};
    }
  } else {
    unsigned int n0 = n - 1;
    if (m <= 0) {
      throw std::logic_error("absurd case");
    } else {
      unsigned int n1 = m - 1;
      return nat_le_of_lt(n0, n1, _H);
    }
  }
}

unsigned int
Dim10TowerProofChainCase::qpos_denom(const Dim10TowerProofChainCase::QPos &q) {
  return (q.qpos_denom_pred + 1);
}

Dim10TowerProofChainCase::QPos
Dim10TowerProofChainCase::nat_to_qpos(unsigned int n) {
  return QPos{n, 0u};
}

unsigned int Dim10TowerProofChainCase::nat_sub(unsigned int n, unsigned int m) {
  if (n <= 0) {
    return 0u;
  } else {
    unsigned int n_ = n - 1;
    if (m <= 0) {
      return (n_ + 1);
    } else {
      unsigned int m_ = m - 1;
      return nat_sub(n_, m_);
    }
  }
}

unsigned int Dim10TowerProofChainCase::poly_approx_dim(unsigned int _x0,
                                                       unsigned int _x1) {
  return nat_sub(_x0, _x1);
}

unsigned int Dim10TowerProofChainCase::layer_dim(unsigned int base_dim,
                                                 unsigned int n) {
  return nat_sub(poly_approx_dim(base_dim, n),
                 poly_approx_dim(base_dim, (n + 1)));
}

Dim10TowerProofChainCase::GradedObj
Dim10TowerProofChainCase::layer_obj(unsigned int base_dim, unsigned int n) {
  return GradedObj{layer_dim(base_dim, n)};
}

Dim10TowerProofChainCase::QPos
Dim10TowerProofChainCase::layer_measure(unsigned int base_dim, unsigned int n) {
  return nat_to_qpos(layer_dim(base_dim, n));
}

Dim10TowerProofChainCase::EventuallyZero
Dim10TowerProofChainCase::layer_measure_eventually_zero(unsigned int base_dim) {
  return SigT<unsigned int, std::any>::existt(base_dim, std::any{});
}

Dim10TowerProofChainCase::GradedObj Dim10TowerProofChainCase::P_n_obj(
    unsigned int n, const Dim10TowerProofChainCase::GradedObj &x) {
  return GradedObj{poly_approx_dim(x.go_dim, n)};
}

Dim10TowerProofChainCase::GradedObj
Dim10TowerProofChainCase::D_n_obj(unsigned int _x0, unsigned int _x1) {
  return layer_obj(_x0, _x1);
}

Dim10TowerProofChainCase::QPos
Dim10TowerProofChainCase::D_n_measure(unsigned int _x0, unsigned int _x1) {
  return layer_measure(_x0, _x1);
}

Dim10TowerProofChainCase::EventuallyZero
Dim10TowerProofChainCase::D_n_measure_eventually_zero(unsigned int _x0) {
  return layer_measure_eventually_zero(_x0);
}

Dim10TowerProofChainCase::GradedGoodwillieTower
Dim10TowerProofChainCase::make_graded_goodwillie_tower(unsigned int base_dim) {
  return GradedGoodwillieTower{
      [=](unsigned int n) mutable { return P_n_obj(n, GradedObj{base_dim}); },
      [=](unsigned int n) mutable { return D_n_obj(base_dim, n); }};
}

SigT<unsigned int, std::any>
Dim10TowerProofChainCase::graded_goodwillie_layers_stabilize(
    unsigned int base_dim) {
  SigT<unsigned int, std::any> e = D_n_measure_eventually_zero(base_dim);
  auto &[d_x, d_a1] =
      std::get<typename SigT<unsigned int, std::any>::ExistT>(e.v_mut());
  return SigT<unsigned int, std::any>::existt(d_x, std::any{});
}

SigT<unsigned int, std::any>
Dim10TowerProofChainCase::graded_goodwillie_P_stabilizes(
    unsigned int base_dim) {
  return SigT<unsigned int, std::any>::existt(base_dim, std::any{});
}

std::pair<std::pair<std::pair<Dim10TowerProofChainCase::IsIntegerValued,
                              Dim10TowerProofChainCase::EventuallyZero>,
                    SigT<unsigned int, std::any>>,
          SigT<unsigned int, std::any>>
Dim10TowerProofChainCase::graded_complete_proof_chain(unsigned int base_dim) {
  return std::make_pair(
      std::make_pair(
          std::make_pair(std::any{}, D_n_measure_eventually_zero(base_dim)),
          graded_goodwillie_layers_stabilize(base_dim)),
      graded_goodwillie_P_stabilizes(base_dim));
}

Dim10TowerProofChainCase::GoodwillieProofChain
Dim10TowerProofChainCase::make_goodwillie_proof_chain(unsigned int base_dim) {
  return GoodwillieProofChain{D_n_measure_eventually_zero(base_dim),
                              graded_goodwillie_layers_stabilize(base_dim),
                              graded_goodwillie_P_stabilizes(base_dim)};
}
