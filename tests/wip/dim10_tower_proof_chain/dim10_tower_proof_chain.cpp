#include <dim10_tower_proof_chain.h>

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

__attribute__((pure)) Dim10TowerProofChainCase::nat_le
Dim10TowerProofChainCase::nat_le_of_lt(const unsigned int n,
                                       const unsigned int m,
                                       const std::any _H) {
  if (n <= 0) {
    if (m <= 0) {
      return Unit::e_TT;
    } else {
      unsigned int _x = m - 1;
      return Unit::e_TT;
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

__attribute__((pure)) unsigned int Dim10TowerProofChainCase::qpos_denom(
    std::shared_ptr<Dim10TowerProofChainCase::QPos> q) {
  return (std::move(q)->qpos_denom_pred + 1);
}

std::shared_ptr<Dim10TowerProofChainCase::QPos>
Dim10TowerProofChainCase::nat_to_qpos(const unsigned int n) {
  return std::make_shared<Dim10TowerProofChainCase::QPos>(
      QPos{std::move(n), 0u});
}

__attribute__((pure)) unsigned int
Dim10TowerProofChainCase::nat_sub(const unsigned int n, const unsigned int m) {
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

__attribute__((pure)) unsigned int
Dim10TowerProofChainCase::poly_approx_dim(const unsigned int _x0,
                                          const unsigned int _x1) {
  return nat_sub(_x0, _x1);
}

__attribute__((pure)) unsigned int
Dim10TowerProofChainCase::layer_dim(const unsigned int base_dim,
                                    const unsigned int n) {
  return nat_sub(poly_approx_dim(base_dim, n),
                 poly_approx_dim(base_dim, (n + 1)));
}

std::shared_ptr<Dim10TowerProofChainCase::GradedObj>
Dim10TowerProofChainCase::layer_obj(const unsigned int base_dim,
                                    const unsigned int n) {
  return std::make_shared<Dim10TowerProofChainCase::GradedObj>(
      GradedObj{layer_dim(std::move(base_dim), std::move(n))});
}

std::shared_ptr<Dim10TowerProofChainCase::QPos>
Dim10TowerProofChainCase::layer_measure(const unsigned int base_dim,
                                        const unsigned int n) {
  return nat_to_qpos(layer_dim(base_dim, n));
}

__attribute__((pure)) Dim10TowerProofChainCase::EventuallyZero
Dim10TowerProofChainCase::layer_measure_eventually_zero(
    const unsigned int base_dim) {
  return SigT<unsigned int, std::any>::ctor::ExistT_(std::move(base_dim),
                                                     std::any{});
}

std::shared_ptr<Dim10TowerProofChainCase::GradedObj>
Dim10TowerProofChainCase::P_n_obj(
    const unsigned int n,
    std::shared_ptr<Dim10TowerProofChainCase::GradedObj> x) {
  return std::make_shared<Dim10TowerProofChainCase::GradedObj>(
      GradedObj{poly_approx_dim(std::move(x)->go_dim, std::move(n))});
}

std::shared_ptr<Dim10TowerProofChainCase::GradedObj>
Dim10TowerProofChainCase::D_n_obj(const unsigned int _x0,
                                  const unsigned int _x1) {
  return layer_obj(_x0, _x1);
}

std::shared_ptr<Dim10TowerProofChainCase::QPos>
Dim10TowerProofChainCase::D_n_measure(const unsigned int _x0,
                                      const unsigned int _x1) {
  return layer_measure(_x0, _x1);
}

__attribute__((pure)) Dim10TowerProofChainCase::EventuallyZero
Dim10TowerProofChainCase::D_n_measure_eventually_zero(const unsigned int _x0) {
  return layer_measure_eventually_zero(_x0);
}

std::shared_ptr<Dim10TowerProofChainCase::GradedGoodwillieTower>
Dim10TowerProofChainCase::make_graded_goodwillie_tower(
    const unsigned int base_dim) {
  return std::make_shared<Dim10TowerProofChainCase::GradedGoodwillieTower>(
      GradedGoodwillieTower{
          [=](unsigned int n) mutable {
            return P_n_obj(
                n, std::make_shared<Dim10TowerProofChainCase::GradedObj>(
                       GradedObj{base_dim}));
          },
          [=](unsigned int n) mutable { return D_n_obj(base_dim, n); }});
}

std::shared_ptr<SigT<unsigned int, std::any>>
Dim10TowerProofChainCase::graded_goodwillie_layers_stabilize(
    const unsigned int base_dim) {
  std::shared_ptr<SigT<unsigned int, std::any>> e =
      D_n_measure_eventually_zero(base_dim);
  return [&](void) {
    if (std::move(e).use_count() == 1 && std::move(e)->v().index() == 0) {
      auto &_rf = std::get<0>(std::move(e)->v_mut());
      unsigned int x = std::move(_rf.d_a0);
      _rf.d_a0 = x;
      _rf.d_a1 = ([]() -> std::any {
        throw std::logic_error("unreachable");
        return std::any{};
      })();
      return std::move(e);
    } else {
      return std::visit(
          Overloaded{
              [](const typename SigT<unsigned int, std::any>::ExistT _args)
                  -> std::shared_ptr<SigT<unsigned int, std::any>> {
                return SigT<unsigned int, std::any>::ctor::ExistT_(_args.d_a0,
                                                                   std::any{});
              }},
          std::move(e)->v());
    }
  }();
}

std::shared_ptr<SigT<unsigned int, std::any>>
Dim10TowerProofChainCase::graded_goodwillie_P_stabilizes(
    const unsigned int base_dim) {
  return SigT<unsigned int, std::any>::ctor::ExistT_(std::move(base_dim),
                                                     std::any{});
}

__attribute__((pure))
std::pair<std::pair<std::pair<Dim10TowerProofChainCase::IsIntegerValued,
                              Dim10TowerProofChainCase::EventuallyZero>,
                    std::shared_ptr<SigT<unsigned int, std::any>>>,
          std::shared_ptr<SigT<unsigned int, std::any>>>
Dim10TowerProofChainCase::graded_complete_proof_chain(
    const unsigned int base_dim) {
  return std::make_pair(
      std::make_pair(std::make_pair(([]() -> std::any {
                                      throw std::logic_error("unreachable");
                                      return std::any{};
                                    })(),
                                    D_n_measure_eventually_zero(base_dim)),
                     graded_goodwillie_layers_stabilize(base_dim)),
      graded_goodwillie_P_stabilizes(base_dim));
}

std::shared_ptr<Dim10TowerProofChainCase::GoodwillieProofChain>
Dim10TowerProofChainCase::make_goodwillie_proof_chain(
    const unsigned int base_dim) {
  return std::make_shared<Dim10TowerProofChainCase::GoodwillieProofChain>(
      GoodwillieProofChain{D_n_measure_eventually_zero(base_dim),
                           graded_goodwillie_layers_stabilize(base_dim),
                           graded_goodwillie_P_stabilizes(base_dim)});
}
