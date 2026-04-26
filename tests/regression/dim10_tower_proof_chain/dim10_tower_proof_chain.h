#ifndef INCLUDED_DIM10_TOWER_PROOF_CHAIN
#define INCLUDED_DIM10_TOWER_PROOF_CHAIN

#include <any>
#include <functional>
#include <memory>
#include <optional>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

template <typename T> struct is_unique_ptr : std::false_type {};

template <typename T>
struct is_unique_ptr<std::unique_ptr<T>> : std::true_type {
  using element_type = T;
};

template <typename T> auto clone_value(const T &x) { return x; }

template <typename T>
std::unique_ptr<T> clone_value(const std::unique_ptr<T> &x) {
  if constexpr (requires { x->clone(); }) {
    return x ? std::make_unique<T>(x->clone()) : nullptr;
  } else {
    return x ? std::make_unique<T>(*x) : nullptr;
  }
}

template <typename Target, typename Source>
Target clone_as_value(const Source &x) {
  using T = std::remove_cvref_t<Target>;
  using S = std::remove_cvref_t<Source>;
  if constexpr (requires(const S &s) {
                  s.has_value();
                  *s;
                }) {
    if (!x.has_value())
      return T{};
    using TInner = std::remove_cvref_t<decltype(*std::declval<const T &>())>;
    return T{clone_as_value<TInner>(*x)};
  } else if constexpr (std::is_same_v<T, S>) {
    if constexpr (is_unique_ptr<T>::value) {
      return clone_value(x);
    } else if constexpr (requires { x.clone(); }) {
      return x.clone();
    } else {
      return x;
    }
  } else if constexpr (is_unique_ptr<S>::value) {
    if (!x)
      return T{};
    return clone_as_value<T>(*x);
  } else if constexpr (is_unique_ptr<T>::value) {
    using Inner = typename is_unique_ptr<T>::element_type;
    return std::make_unique<Inner>(clone_as_value<Inner>(x));
  } else {
    return T(x);
  }
}

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
  SigT() {}

  explicit SigT(ExistT _v) : d_v_(std::move(_v)) {}

  SigT(const SigT<t_A, t_P> &_other) : d_v_(std::move(_other.clone().d_v_)) {}

  SigT(SigT<t_A, t_P> &&_other) : d_v_(std::move(_other.d_v_)) {}

  __attribute__((pure)) SigT<t_A, t_P> &
  operator=(const SigT<t_A, t_P> &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  __attribute__((pure)) SigT<t_A, t_P> &operator=(SigT<t_A, t_P> &&_other) {
    d_v_ = std::move(_other.d_v_);
    return *this;
  }

  // ACCESSORS
  __attribute__((pure)) SigT<t_A, t_P> clone() const {
    auto &&_sv = *(this);
    const auto &[d_x, d_a1] = std::get<ExistT>(_sv.v());
    return SigT<t_A, t_P>(ExistT{clone_value(d_x), clone_value(d_a1)});
  }

  // CREATORS
  template <typename _U0, typename _U1>
  explicit SigT(const SigT<_U0, _U1> &_other) {
    const auto &[d_x, d_a1] =
        std::get<typename SigT<_U0, _U1>::ExistT>(_other.v());
    d_v_ = ExistT{clone_as_value<t_A>(d_x), clone_as_value<t_P>(d_a1)};
  }

  __attribute__((pure)) static SigT<t_A, t_P> existt(t_A x, t_P a1) {
    return SigT(ExistT{std::move(x), std::move(a1)});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) SigT<t_A, t_P> *operator->() { return this; }

  __attribute__((pure)) const SigT<t_A, t_P> *operator->() const {
    return this;
  }

  __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

  __attribute__((pure)) bool operator==(std::nullptr_t) const { return false; }

  // MANIPULATORS
  void reset() { *this = SigT<t_A, t_P>(); }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
};

struct Dim10TowerProofChainCase {
  using nat_lt = std::any;
  using nat_le = std::any;
  static nat_le nat_le_of_lt(const unsigned int &n, const unsigned int &m,
                             const std::any _H);

  struct QPos {
    unsigned int qpos_num;
    unsigned int qpos_denom_pred;

    __attribute__((pure)) QPos *operator->() { return this; }

    __attribute__((pure)) const QPos *operator->() const { return this; }

    // ACCESSORS
    __attribute__((pure)) QPos clone() const {
      return QPos{(*(this)).qpos_num, (*(this)).qpos_denom_pred};
    }
  };

  __attribute__((pure)) static unsigned int qpos_denom(const QPos &q);
  __attribute__((pure)) static QPos nat_to_qpos(unsigned int n);
  using EventuallyZero = SigT<unsigned int, std::any>;
  using IsIntegerValued = std::any;

  struct GradedObj {
    unsigned int go_dim;

    __attribute__((pure)) GradedObj *operator->() { return this; }

    __attribute__((pure)) const GradedObj *operator->() const { return this; }

    // ACCESSORS
    __attribute__((pure)) GradedObj clone() const {
      return GradedObj{(*(this)).go_dim};
    }
  };

  static inline const GradedObj go_zero = GradedObj{0u};
  __attribute__((pure)) static unsigned int nat_sub(const unsigned int &n,
                                                    const unsigned int &m);
  __attribute__((pure)) static unsigned int
  poly_approx_dim(const unsigned int &_x0, const unsigned int &_x1);
  __attribute__((pure)) static unsigned int
  layer_dim(const unsigned int &base_dim, unsigned int n);
  __attribute__((pure)) static GradedObj layer_obj(const unsigned int &base_dim,
                                                   const unsigned int &n);
  __attribute__((pure)) static QPos layer_measure(const unsigned int &base_dim,
                                                  const unsigned int &n);
  __attribute__((pure)) static EventuallyZero
  layer_measure_eventually_zero(unsigned int base_dim);
  __attribute__((pure)) static GradedObj P_n_obj(const unsigned int &n,
                                                 const GradedObj &x);
  __attribute__((pure)) static GradedObj D_n_obj(const unsigned int &_x0,
                                                 const unsigned int &_x1);
  __attribute__((pure)) static QPos D_n_measure(const unsigned int &_x0,
                                                const unsigned int &_x1);
  __attribute__((pure)) static EventuallyZero
  D_n_measure_eventually_zero(const unsigned int &_x0);

  struct GradedGoodwillieTower {
    std::function<GradedObj(unsigned int)> ggt_P;
    std::function<GradedObj(unsigned int)> ggt_D;

    __attribute__((pure)) GradedGoodwillieTower *operator->() { return this; }

    __attribute__((pure)) const GradedGoodwillieTower *operator->() const {
      return this;
    }

    // ACCESSORS
    __attribute__((pure)) GradedGoodwillieTower clone() const {
      return GradedGoodwillieTower{(*(this)).ggt_P, (*(this)).ggt_D};
    }
  };

  __attribute__((pure)) static GradedGoodwillieTower
  make_graded_goodwillie_tower(unsigned int base_dim);
  __attribute__((pure)) static SigT<unsigned int, std::any>
  graded_goodwillie_layers_stabilize(const unsigned int &base_dim);
  __attribute__((pure)) static SigT<unsigned int, std::any>
  graded_goodwillie_P_stabilizes(unsigned int base_dim);
  static inline const GradedGoodwillieTower dim10_tower =
      make_graded_goodwillie_tower(10u);
  static inline const SigT<unsigned int, std::any> dim10_layers_stabilize =
      []() {
        SigT<unsigned int, std::any> s =
            graded_goodwillie_layers_stabilize(10u);
        const auto &[d_x, d_a1] =
            std::get<typename SigT<unsigned int, std::any>::ExistT>(s.v());
        return SigT<unsigned int, std::any>::existt(d_x, std::any{});
      }();
  static inline const SigT<unsigned int, std::any> dim10_P_stabilizes = []() {
    SigT<unsigned int, std::any> s = graded_goodwillie_P_stabilizes(10u);
    const auto &[d_x, d_a1] =
        std::get<typename SigT<unsigned int, std::any>::ExistT>(s.v());
    return SigT<unsigned int, std::any>::existt(d_x, std::any{});
  }();
  __attribute__((pure)) static std::pair<
      std::pair<std::pair<IsIntegerValued, EventuallyZero>,
                SigT<unsigned int, std::any>>,
      SigT<unsigned int, std::any>>
  graded_complete_proof_chain(const unsigned int &base_dim);

  struct GoodwillieProofChain {
    EventuallyZero gc_eventually_zero;
    SigT<unsigned int, std::any> gc_layers_stabilize;
    SigT<unsigned int, std::any> gc_P_stabilize;

    __attribute__((pure)) GoodwillieProofChain *operator->() { return this; }

    __attribute__((pure)) const GoodwillieProofChain *operator->() const {
      return this;
    }

    // ACCESSORS
    __attribute__((pure)) GoodwillieProofChain clone() const {
      return GoodwillieProofChain{(*(this)).gc_eventually_zero,
                                  (*(this)).gc_layers_stabilize,
                                  (*(this)).gc_P_stabilize};
    }
  };

  __attribute__((pure)) static GoodwillieProofChain
  make_goodwillie_proof_chain(const unsigned int &base_dim);
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

    __attribute__((pure)) Dim10Bundle *operator->() { return this; }

    __attribute__((pure)) const Dim10Bundle *operator->() const { return this; }

    // ACCESSORS
    __attribute__((pure)) Dim10Bundle clone() const {
      return Dim10Bundle{(*(this)).dt_tower, (*(this)).dt_chain};
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
    auto &&_sv = dim10_bundle.dt_chain.gc_layers_stabilize;
    const auto &[d_x, d_a1] =
        std::get<typename SigT<unsigned int, std::any>::ExistT>(_sv.v());
    return d_x;
  }();
  static inline const unsigned int dim10_P_cutoff = []() {
    auto &&_sv0 = dim10_bundle.dt_chain.gc_P_stabilize;
    const auto &[d_x0, d_a10] =
        std::get<typename SigT<unsigned int, std::any>::ExistT>(_sv0.v());
    return d_x0;
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
