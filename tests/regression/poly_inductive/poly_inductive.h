#ifndef INCLUDED_POLY_INDUCTIVE
#define INCLUDED_POLY_INDUCTIVE

#include <memory>
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

template <typename T> struct is_shared_ptr : std::false_type {};

template <typename T>
struct is_shared_ptr<std::shared_ptr<T>> : std::true_type {
  using element_type = T;
};

template <typename T> auto clone_value(const T &x) { return x; }

template <typename T>
std::unique_ptr<T> clone_value(const std::unique_ptr<T> &x) {
  return x ? std::make_unique<T>(x->clone()) : nullptr;
}

template <typename T>
std::shared_ptr<T> clone_value(const std::shared_ptr<T> &x) {
  if constexpr (requires { x->clone(); }) {
    return x ? std::make_shared<T>(x->clone()) : nullptr;
  } else {
    return x;
  }
}

template <typename Target, typename Source>
Target clone_as_value(const Source &x) {
  using TargetBare = std::remove_cvref_t<Target>;
  using SourceBare = std::remove_cvref_t<Source>;
  if constexpr (is_unique_ptr<TargetBare>::value) {
    using Inner = typename is_unique_ptr<TargetBare>::element_type;
    if constexpr (is_unique_ptr<SourceBare>::value) {
      using SourceInner = typename is_unique_ptr<SourceBare>::element_type;
      if (!x)
        return nullptr;
      if constexpr (std::is_same_v<Inner, SourceInner>) {
        return clone_value(x);
      } else if constexpr (requires {
                             typename Inner::crane_element_type;
                             x->template clone_as<
                                 typename Inner::crane_element_type>();
                           }) {
        return std::make_unique<Inner>(
            x->template clone_as<typename Inner::crane_element_type>());
      } else if constexpr (requires { x->template clone_as<Inner>(); }) {
        return std::make_unique<Inner>(x->template clone_as<Inner>());
      } else {
        return std::make_unique<Inner>(x->clone());
      }
    } else {
      if constexpr (std::is_same_v<Inner, SourceBare>) {
        return std::make_unique<Inner>(x.clone());
      } else if constexpr (requires { x.template clone_as<Inner>(); }) {
        return std::make_unique<Inner>(x.template clone_as<Inner>());
      } else {
        return std::make_unique<Inner>(x.clone());
      }
    }
  } else if constexpr (is_shared_ptr<TargetBare>::value) {
    using Inner = typename is_shared_ptr<TargetBare>::element_type;
    if constexpr (is_shared_ptr<SourceBare>::value) {
      using SourceInner = typename is_shared_ptr<SourceBare>::element_type;
      if (!x)
        return nullptr;
      if constexpr (std::is_same_v<Inner, SourceInner>) {
        return clone_value(x);
      } else if constexpr (requires { x->template clone_as<Inner>(); }) {
        return std::make_shared<Inner>(x->template clone_as<Inner>());
      } else {
        return std::make_shared<Inner>(x->clone());
      }
    } else if constexpr (is_unique_ptr<SourceBare>::value) {
      if (!x)
        return nullptr;
      if constexpr (requires { x->template clone_as<Inner>(); }) {
        return std::make_shared<Inner>(x->template clone_as<Inner>());
      } else {
        return std::make_shared<Inner>(x->clone());
      }
    } else {
      if constexpr (std::is_same_v<Inner, SourceBare>) {
        return std::make_shared<Inner>(x.clone());
      } else if constexpr (requires { x.template clone_as<Inner>(); }) {
        return std::make_shared<Inner>(x.template clone_as<Inner>());
      } else {
        return std::make_shared<Inner>(x.clone());
      }
    }
  } else if constexpr (std::is_same_v<TargetBare, SourceBare>) {
    return clone_value(x);
  } else if constexpr (is_unique_ptr<SourceBare>::value) {
    using SourceInner = typename is_unique_ptr<SourceBare>::element_type;
    if constexpr (std::is_same_v<TargetBare, SourceInner>) {
      return x ? x->clone() : Target{};
    } else if constexpr (requires { x->template clone_as<TargetBare>(); }) {
      return x->template clone_as<TargetBare>();
    } else {
      return Target(*x);
    }
  } else if constexpr (is_shared_ptr<SourceBare>::value) {
    using SourceInner = typename is_shared_ptr<SourceBare>::element_type;
    if constexpr (std::is_same_v<TargetBare, SourceInner>) {
      return x ? x->clone() : Target{};
    } else if constexpr (requires { x->template clone_as<TargetBare>(); }) {
      return x->template clone_as<TargetBare>();
    } else {
      return Target(*x);
    }
  } else if constexpr (requires {
                         typename TargetBare::crane_element_type;
                         x.template clone_as<
                             typename TargetBare::crane_element_type>();
                       }) {
    return x.template clone_as<typename TargetBare::crane_element_type>();
  } else if constexpr (requires { x.template clone_as<TargetBare>(); }) {
    return x.template clone_as<TargetBare>();
  } else {
    return Target(x);
  }
}

struct PolyInductive {
  template <typename t_A> struct pbox {
    // TYPES
    struct PBox {
      t_A d_a0;
    };

    using variant_t = std::variant<PBox>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    pbox() {}

    explicit pbox(PBox _v) : d_v_(std::move(_v)) {}

    pbox(const pbox<t_A> &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    pbox(pbox<t_A> &&_other) : d_v_(std::move(_other.d_v_)) {}

    __attribute__((pure)) pbox<t_A> &operator=(const pbox<t_A> &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    __attribute__((pure)) pbox<t_A> &operator=(pbox<t_A> &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) pbox<t_A> clone() const {
      auto &&_sv = *(this);
      const auto &[d_a0] = std::get<PBox>(_sv.v());
      return pbox<t_A>(PBox{clone_as_value<t_A>(d_a0)});
    }

    template <typename _CloneT0>
    __attribute__((pure)) pbox<_CloneT0> clone_as() const {
      auto &&_sv = *(this);
      const auto &[d_a0] = std::get<PBox>(_sv.v());
      return pbox<_CloneT0>(
          typename pbox<_CloneT0>::PBox{clone_as_value<_CloneT0>(d_a0)});
    }

    // CREATORS
    __attribute__((pure)) static pbox<t_A> PBox_(t_A a0) {
      return pbox(PBox{std::move(a0)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) pbox<t_A> *operator->() { return this; }

    __attribute__((pure)) const pbox<t_A> *operator->() const { return this; }

    __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

    __attribute__((pure)) bool operator==(std::nullptr_t) const {
      return false;
    }

    // MANIPULATORS
    void reset() { *this = pbox<t_A>(); }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    t_A punbox() const {
      auto &&_sv = *(this);
      const auto &[d_a0] = std::get<typename pbox<t_A>::PBox>(_sv.v());
      return d_a0;
    }

    template <typename T1, MapsTo<T1, t_A> F0> T1 pbox_rec(F0 &&f) const {
      auto &&_sv = *(this);
      const auto &[d_a0] = std::get<typename pbox<t_A>::PBox>(_sv.v());
      return f(d_a0);
    }

    template <typename T1, MapsTo<T1, t_A> F0> T1 pbox_rect(F0 &&f) const {
      auto &&_sv = *(this);
      const auto &[d_a0] = std::get<typename pbox<t_A>::PBox>(_sv.v());
      return f(d_a0);
    }
  };

  template <typename t_A, typename t_B> struct ppair {
    // TYPES
    struct PPair {
      t_A d_a0;
      t_B d_a1;
    };

    using variant_t = std::variant<PPair>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    ppair() {}

    explicit ppair(PPair _v) : d_v_(std::move(_v)) {}

    ppair(const ppair<t_A, t_B> &_other)
        : d_v_(std::move(_other.clone().d_v_)) {}

    ppair(ppair<t_A, t_B> &&_other) : d_v_(std::move(_other.d_v_)) {}

    __attribute__((pure)) ppair<t_A, t_B> &
    operator=(const ppair<t_A, t_B> &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    __attribute__((pure)) ppair<t_A, t_B> &operator=(ppair<t_A, t_B> &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) ppair<t_A, t_B> clone() const {
      auto &&_sv = *(this);
      const auto &[d_a0, d_a1] = std::get<PPair>(_sv.v());
      return ppair<t_A, t_B>(
          PPair{clone_as_value<t_A>(d_a0), clone_as_value<t_B>(d_a1)});
    }

    template <typename _CloneT0, typename _CloneT1>
    __attribute__((pure)) ppair<_CloneT0, _CloneT1> clone_as() const {
      auto &&_sv = *(this);
      const auto &[d_a0, d_a1] = std::get<PPair>(_sv.v());
      return ppair<_CloneT0, _CloneT1>(
          typename ppair<_CloneT0, _CloneT1>::PPair{
              clone_as_value<_CloneT0>(d_a0), clone_as_value<_CloneT1>(d_a1)});
    }

    // CREATORS
    __attribute__((pure)) static ppair<t_A, t_B> PPair_(t_A a0, t_B a1) {
      return ppair(PPair{std::move(a0), std::move(a1)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) ppair<t_A, t_B> *operator->() { return this; }

    __attribute__((pure)) const ppair<t_A, t_B> *operator->() const {
      return this;
    }

    __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

    __attribute__((pure)) bool operator==(std::nullptr_t) const {
      return false;
    }

    // MANIPULATORS
    void reset() { *this = ppair<t_A, t_B>(); }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    t_B psnd() const {
      auto &&_sv = *(this);
      const auto &[d_a0, d_a1] =
          std::get<typename ppair<t_A, t_B>::PPair>(_sv.v());
      return d_a1;
    }

    t_A pfst() const {
      auto &&_sv = *(this);
      const auto &[d_a0, d_a1] =
          std::get<typename ppair<t_A, t_B>::PPair>(_sv.v());
      return d_a0;
    }

    template <typename T1, MapsTo<T1, t_A, t_B> F0> T1 ppair_rec(F0 &&f) const {
      auto &&_sv = *(this);
      const auto &[d_a0, d_a1] =
          std::get<typename ppair<t_A, t_B>::PPair>(_sv.v());
      return f(d_a0, d_a1);
    }

    template <typename T1, MapsTo<T1, t_A, t_B> F0>
    T1 ppair_rect(F0 &&f) const {
      auto &&_sv = *(this);
      const auto &[d_a0, d_a1] =
          std::get<typename ppair<t_A, t_B>::PPair>(_sv.v());
      return f(d_a0, d_a1);
    }
  };

  template <typename t_A> struct pmaybe {
    // TYPES
    struct PNothing {};

    struct PJust {
      t_A d_a0;
    };

    using variant_t = std::variant<PNothing, PJust>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    pmaybe() {}

    explicit pmaybe(PNothing _v) : d_v_(_v) {}

    explicit pmaybe(PJust _v) : d_v_(std::move(_v)) {}

    pmaybe(const pmaybe<t_A> &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    pmaybe(pmaybe<t_A> &&_other) : d_v_(std::move(_other.d_v_)) {}

    __attribute__((pure)) pmaybe<t_A> &operator=(const pmaybe<t_A> &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    __attribute__((pure)) pmaybe<t_A> &operator=(pmaybe<t_A> &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) pmaybe<t_A> clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<PNothing>(_sv.v())) {
        return pmaybe<t_A>(PNothing{});
      } else {
        const auto &[d_a0] = std::get<PJust>(_sv.v());
        return pmaybe<t_A>(PJust{clone_as_value<t_A>(d_a0)});
      }
    }

    template <typename _CloneT0>
    __attribute__((pure)) pmaybe<_CloneT0> clone_as() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<PNothing>(_sv.v())) {
        return pmaybe<_CloneT0>(typename pmaybe<_CloneT0>::PNothing{});
      } else {
        const auto &[d_a0] = std::get<PJust>(_sv.v());
        return pmaybe<_CloneT0>(
            typename pmaybe<_CloneT0>::PJust{clone_as_value<_CloneT0>(d_a0)});
      }
    }

    // CREATORS
    constexpr static pmaybe<t_A> pnothing() { return pmaybe(PNothing{}); }

    __attribute__((pure)) static pmaybe<t_A> pjust(t_A a0) {
      return pmaybe(PJust{std::move(a0)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) pmaybe<t_A> *operator->() { return this; }

    __attribute__((pure)) const pmaybe<t_A> *operator->() const { return this; }

    __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

    __attribute__((pure)) bool operator==(std::nullptr_t) const {
      return false;
    }

    // MANIPULATORS
    void reset() { *this = pmaybe<t_A>(); }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    t_A pmaybe_default(const t_A d) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename pmaybe<t_A>::PNothing>(_sv.v())) {
        return d;
      } else {
        const auto &[d_a0] = std::get<typename pmaybe<t_A>::PJust>(_sv.v());
        return d_a0;
      }
    }

    template <typename T1, MapsTo<T1, t_A> F0>
    __attribute__((pure)) pmaybe<T1> pmaybe_map(F0 &&f) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename pmaybe<t_A>::PNothing>(_sv.v())) {
        return pmaybe<T1>::pnothing();
      } else {
        const auto &[d_a0] = std::get<typename pmaybe<t_A>::PJust>(_sv.v());
        return pmaybe<T1>::pjust(f(d_a0));
      }
    }

    template <typename T1, MapsTo<T1, t_A> F1>
    T1 pmaybe_rec(const T1 f, F1 &&f0) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename pmaybe<t_A>::PNothing>(_sv.v())) {
        return f;
      } else {
        const auto &[d_a0] = std::get<typename pmaybe<t_A>::PJust>(_sv.v());
        return f0(d_a0);
      }
    }

    template <typename T1, MapsTo<T1, t_A> F1>
    T1 pmaybe_rect(const T1 f, F1 &&f0) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename pmaybe<t_A>::PNothing>(_sv.v())) {
        return f;
      } else {
        const auto &[d_a0] = std::get<typename pmaybe<t_A>::PJust>(_sv.v());
        return f0(d_a0);
      }
    }
  };

  template <typename t_A> struct ptree {
    // TYPES
    struct PLeaf {
      t_A d_a0;
    };

    struct PNode {
      std::unique_ptr<ptree<t_A>> d_a0;
      std::unique_ptr<ptree<t_A>> d_a1;
    };

    using variant_t = std::variant<PLeaf, PNode>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    ptree() {}

    explicit ptree(PLeaf _v) : d_v_(std::move(_v)) {}

    explicit ptree(PNode _v) : d_v_(std::move(_v)) {}

    ptree(const ptree<t_A> &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    ptree(ptree<t_A> &&_other) : d_v_(std::move(_other.d_v_)) {}

    __attribute__((pure)) ptree<t_A> &operator=(const ptree<t_A> &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    __attribute__((pure)) ptree<t_A> &operator=(ptree<t_A> &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) ptree<t_A> clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<PLeaf>(_sv.v())) {
        const auto &[d_a0] = std::get<PLeaf>(_sv.v());
        return ptree<t_A>(PLeaf{clone_as_value<t_A>(d_a0)});
      } else {
        const auto &[d_a0, d_a1] = std::get<PNode>(_sv.v());
        return ptree<t_A>(
            PNode{clone_as_value<std::unique_ptr<ptree<t_A>>>(d_a0),
                  clone_as_value<std::unique_ptr<ptree<t_A>>>(d_a1)});
      }
    }

    template <typename _CloneT0>
    __attribute__((pure)) ptree<_CloneT0> clone_as() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<PLeaf>(_sv.v())) {
        const auto &[d_a0] = std::get<PLeaf>(_sv.v());
        return ptree<_CloneT0>(
            typename ptree<_CloneT0>::PLeaf{clone_as_value<_CloneT0>(d_a0)});
      } else {
        const auto &[d_a0, d_a1] = std::get<PNode>(_sv.v());
        return ptree<_CloneT0>(typename ptree<_CloneT0>::PNode{
            clone_as_value<std::unique_ptr<ptree<_CloneT0>>>(d_a0),
            clone_as_value<std::unique_ptr<ptree<_CloneT0>>>(d_a1)});
      }
    }

    // CREATORS
    __attribute__((pure)) static ptree<t_A> pleaf(t_A a0) {
      return ptree(PLeaf{std::move(a0)});
    }

    __attribute__((pure)) static ptree<t_A> pnode(const ptree<t_A> &a0,
                                                  const ptree<t_A> &a1) {
      return ptree(PNode{std::make_unique<ptree<t_A>>(a0.clone()),
                         std::make_unique<ptree<t_A>>(a1.clone())});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) ptree<t_A> *operator->() { return this; }

    __attribute__((pure)) const ptree<t_A> *operator->() const { return this; }

    __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

    __attribute__((pure)) bool operator==(std::nullptr_t) const {
      return false;
    }

    // MANIPULATORS
    void reset() { *this = ptree<t_A>(); }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    __attribute__((pure)) unsigned int ptree_size() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename ptree<t_A>::PLeaf>(_sv.v())) {
        return 1u;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename ptree<t_A>::PNode>(_sv.v());
        return (((*(d_a0)).ptree_size() + (*(d_a1)).ptree_size()) + 1);
      }
    }

    template <typename T1, MapsTo<T1, t_A> F0,
              MapsTo<T1, ptree<t_A>, T1, ptree<t_A>, T1> F1>
    T1 ptree_rec(F0 &&f, F1 &&f0) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename ptree<t_A>::PLeaf>(_sv.v())) {
        const auto &[d_a0] = std::get<typename ptree<t_A>::PLeaf>(_sv.v());
        return f(d_a0);
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename ptree<t_A>::PNode>(_sv.v());
        return f0(*(d_a0), (*(d_a0)).template ptree_rec<T1>(f, f0), *(d_a1),
                  (*(d_a1)).template ptree_rec<T1>(f, f0));
      }
    }

    template <typename T1, MapsTo<T1, t_A> F0,
              MapsTo<T1, ptree<t_A>, T1, ptree<t_A>, T1> F1>
    T1 ptree_rect(F0 &&f, F1 &&f0) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename ptree<t_A>::PLeaf>(_sv.v())) {
        const auto &[d_a0] = std::get<typename ptree<t_A>::PLeaf>(_sv.v());
        return f(d_a0);
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename ptree<t_A>::PNode>(_sv.v());
        return f0(*(d_a0), (*(d_a0)).template ptree_rect<T1>(f, f0), *(d_a1),
                  (*(d_a1)).template ptree_rect<T1>(f, f0));
      }
    }
  };

  static inline const unsigned int test_pbox =
      pbox<unsigned int>::PBox_(42u).punbox();
  static inline const unsigned int test_ppair_fst =
      ppair<unsigned int, bool>::PPair_(7u, true).pfst();
  static inline const bool test_ppair_snd =
      ppair<unsigned int, bool>::PPair_(7u, true).psnd();
  static inline const unsigned int test_pjust =
      pmaybe<unsigned int>::pjust(99u).pmaybe_default(0u);
  static inline const unsigned int test_pnothing =
      pmaybe<unsigned int>::pnothing().pmaybe_default(0u);
  static inline const unsigned int test_pmap =
      pmaybe<unsigned int>::pjust(5u)
          .template pmaybe_map<unsigned int>(
              [](unsigned int x) { return (x + 1); })
          .pmaybe_default(0u);
  static inline const unsigned int test_ptree =
      ptree<unsigned int>::pnode(
          ptree<unsigned int>::pleaf(1u),
          ptree<unsigned int>::pnode(ptree<unsigned int>::pleaf(2u),
                                     ptree<unsigned int>::pleaf(3u)))
          .ptree_size();
};

#endif // INCLUDED_POLY_INDUCTIVE
