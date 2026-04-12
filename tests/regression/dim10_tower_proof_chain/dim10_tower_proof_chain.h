#ifndef INCLUDED_DIM10_TOWER_PROOF_CHAIN
#define INCLUDED_DIM10_TOWER_PROOF_CHAIN

#include <any>
#include <functional>
#include <memory>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

template <typename t_A, typename t_P> struct SigT {
  // TYPES
  struct ExistT {
    t_A d_x;
    t_P d_a1;
  };

  using variant_t = std::variant<ExistT>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  explicit SigT(ExistT _v) : d_v_(std::move(_v)) {}

  static std::shared_ptr<SigT<t_A, t_P>> existt(t_A x, t_P a1) {
    return std::make_shared<SigT<t_A, t_P>>(
        ExistT{std::move(x), std::move(a1)});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
};

struct Dim10TowerProofChainCase {
  using nat_lt = std::any;
  using nat_le = std::any;
  __attribute__((pure)) static nat_le
  nat_le_of_lt(const unsigned int n, const unsigned int m, const std::any _H);

  struct QPos {
    unsigned int qpos_num;
    unsigned int qpos_denom_pred;
  };

  __attribute__((pure)) static unsigned int
  qpos_denom(const std::shared_ptr<QPos> &q);
  static std::shared_ptr<QPos> nat_to_qpos(const unsigned int n);
  using EventuallyZero = std::shared_ptr<SigT<unsigned int, std::any>>;
  using IsIntegerValued = std::any;

  struct GradedObj {
    unsigned int go_dim;
  };

  static inline const std::shared_ptr<GradedObj> go_zero =
      std::make_shared<GradedObj>(GradedObj{0u});
  __attribute__((pure)) static unsigned int nat_sub(const unsigned int n,
                                                    const unsigned int m);
  __attribute__((pure)) static unsigned int
  poly_approx_dim(const unsigned int _x0, const unsigned int _x1);
  __attribute__((pure)) static unsigned int
  layer_dim(const unsigned int base_dim, const unsigned int n);
  static std::shared_ptr<GradedObj> layer_obj(const unsigned int base_dim,
                                              const unsigned int n);
  static std::shared_ptr<QPos> layer_measure(const unsigned int base_dim,
                                             const unsigned int n);
  __attribute__((pure)) static EventuallyZero
  layer_measure_eventually_zero(const unsigned int base_dim);
  static std::shared_ptr<GradedObj>
  P_n_obj(const unsigned int n, const std::shared_ptr<GradedObj> &x);
  static std::shared_ptr<GradedObj> D_n_obj(const unsigned int _x0,
                                            const unsigned int _x1);
  static std::shared_ptr<QPos> D_n_measure(const unsigned int _x0,
                                           const unsigned int _x1);
  __attribute__((pure)) static EventuallyZero
  D_n_measure_eventually_zero(const unsigned int _x0);

  struct GradedGoodwillieTower {
    std::function<std::shared_ptr<GradedObj>(unsigned int)> ggt_P;
    std::function<std::shared_ptr<GradedObj>(unsigned int)> ggt_D;
  };

  static std::shared_ptr<GradedGoodwillieTower>
  make_graded_goodwillie_tower(const unsigned int base_dim);
  static std::shared_ptr<SigT<unsigned int, std::any>>
  graded_goodwillie_layers_stabilize(const unsigned int base_dim);
  static std::shared_ptr<SigT<unsigned int, std::any>>
  graded_goodwillie_P_stabilizes(const unsigned int base_dim);
  static inline const std::shared_ptr<GradedGoodwillieTower> dim10_tower =
      make_graded_goodwillie_tower(10u);
  static inline const std::shared_ptr<SigT<unsigned int, std::any>>
      dim10_layers_stabilize = []() {
        std::shared_ptr<SigT<unsigned int, std::any>> s =
            graded_goodwillie_layers_stabilize(10u);
        if (s.use_count() == 1 && s->v().index() == 0) {
          auto &_rf = std::get<0>(s->v_mut());
          unsigned int x = std::move(_rf.d_x);
          _rf.d_x = x;
          return s;
        } else {
          return std::visit(
              Overloaded{
                  [](const typename SigT<unsigned int, std::any>::ExistT &_args)
                      -> std::shared_ptr<SigT<unsigned int, std::any>> {
                    return SigT<unsigned int, std::any>::existt(_args.d_x,
                                                                std::any{});
                  }},
              s->v());
        }
      }();
  static inline const std::shared_ptr<SigT<unsigned int, std::any>>
      dim10_P_stabilizes = []() {
        std::shared_ptr<SigT<unsigned int, std::any>> s =
            graded_goodwillie_P_stabilizes(10u);
        if (s.use_count() == 1 && s->v().index() == 0) {
          auto &_rf = std::get<0>(s->v_mut());
          unsigned int x = std::move(_rf.d_x);
          _rf.d_x = x;
          return s;
        } else {
          return std::visit(
              Overloaded{
                  [](const typename SigT<unsigned int, std::any>::ExistT &_args)
                      -> std::shared_ptr<SigT<unsigned int, std::any>> {
                    return SigT<unsigned int, std::any>::existt(_args.d_x,
                                                                std::any{});
                  }},
              s->v());
        }
      }();
  __attribute__((pure)) static std::pair<
      std::pair<std::pair<IsIntegerValued, EventuallyZero>,
                std::shared_ptr<SigT<unsigned int, std::any>>>,
      std::shared_ptr<SigT<unsigned int, std::any>>>
  graded_complete_proof_chain(const unsigned int base_dim);

  struct GoodwillieProofChain {
    EventuallyZero gc_eventually_zero;
    std::shared_ptr<SigT<unsigned int, std::any>> gc_layers_stabilize;
    std::shared_ptr<SigT<unsigned int, std::any>> gc_P_stabilize;
  };

  static std::shared_ptr<GoodwillieProofChain>
  make_goodwillie_proof_chain(const unsigned int base_dim);
  static inline const std::shared_ptr<GoodwillieProofChain> dim10_chain =
      make_goodwillie_proof_chain(10u);
  static inline const std::pair<
      std::pair<std::pair<IsIntegerValued, EventuallyZero>,
                std::shared_ptr<SigT<unsigned int, std::any>>>,
      std::shared_ptr<SigT<unsigned int, std::any>>>
      dim10_pair_chain = graded_complete_proof_chain(10u);

  struct Dim10Bundle {
    std::shared_ptr<GradedGoodwillieTower> dt_tower;
    std::shared_ptr<GoodwillieProofChain> dt_chain;
  };

  static inline const std::shared_ptr<Dim10Bundle> dim10_bundle =
      std::make_shared<Dim10Bundle>(Dim10Bundle{dim10_tower, dim10_chain});
  static inline const unsigned int dim10_p0_dim =
      dim10_bundle->dt_tower->ggt_P(0u)->go_dim;
  static inline const unsigned int dim10_p4_dim =
      dim10_bundle->dt_tower->ggt_P(4u)->go_dim;
  static inline const unsigned int dim10_p9_dim =
      dim10_bundle->dt_tower->ggt_P(9u)->go_dim;
  static inline const unsigned int dim10_p10_dim =
      dim10_bundle->dt_tower->ggt_P(10u)->go_dim;
  static inline const unsigned int dim10_p12_dim =
      dim10_bundle->dt_tower->ggt_P(12u)->go_dim;
  static inline const unsigned int dim10_d0_dim =
      dim10_bundle->dt_tower->ggt_D(0u)->go_dim;
  static inline const unsigned int dim10_d4_dim =
      dim10_bundle->dt_tower->ggt_D(4u)->go_dim;
  static inline const unsigned int dim10_d9_dim =
      dim10_bundle->dt_tower->ggt_D(9u)->go_dim;
  static inline const unsigned int dim10_d10_dim =
      dim10_bundle->dt_tower->ggt_D(10u)->go_dim;
  static inline const unsigned int dim10_layers_cutoff = std::visit(
      Overloaded{[](const typename SigT<unsigned int, std::any>::ExistT &_args)
                     -> unsigned int { return _args.d_x; }},
      dim10_bundle->dt_chain->gc_layers_stabilize->v());
  static inline const unsigned int dim10_P_cutoff = std::visit(
      Overloaded{[](const typename SigT<unsigned int, std::any>::ExistT &_args0)
                     -> unsigned int { return _args0.d_x; }},
      dim10_bundle->dt_chain->gc_P_stabilize->v());
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
