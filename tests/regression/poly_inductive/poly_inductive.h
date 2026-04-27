#ifndef INCLUDED_POLY_INDUCTIVE
#define INCLUDED_POLY_INDUCTIVE

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

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

    pbox<t_A> &operator=(const pbox<t_A> &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    pbox<t_A> &operator=(pbox<t_A> &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) pbox<t_A> clone() const {
      auto &&_sv = *(this);
      const auto &[d_a0] = std::get<PBox>(_sv.v());
      return pbox<t_A>(PBox{d_a0});
    }

    // CREATORS
    template <typename _U> explicit pbox(const pbox<_U> &_other) {
      const auto &[d_a0] = std::get<typename pbox<_U>::PBox>(_other.v());
      d_v_ = PBox{t_A(d_a0)};
    }

    __attribute__((pure)) static pbox<t_A> PBox_(t_A a0) {
      return pbox(PBox{std::move(a0)});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return d_v_; }

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

    ppair<t_A, t_B> &operator=(const ppair<t_A, t_B> &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    ppair<t_A, t_B> &operator=(ppair<t_A, t_B> &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) ppair<t_A, t_B> clone() const {
      auto &&_sv = *(this);
      const auto &[d_a0, d_a1] = std::get<PPair>(_sv.v());
      return ppair<t_A, t_B>(PPair{d_a0, d_a1});
    }

    // CREATORS
    template <typename _U0, typename _U1>
    explicit ppair(const ppair<_U0, _U1> &_other) {
      const auto &[d_a0, d_a1] =
          std::get<typename ppair<_U0, _U1>::PPair>(_other.v());
      d_v_ = PPair{t_A(d_a0), t_B(d_a1)};
    }

    __attribute__((pure)) static ppair<t_A, t_B> PPair_(t_A a0, t_B a1) {
      return ppair(PPair{std::move(a0), std::move(a1)});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return d_v_; }

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

    pmaybe<t_A> &operator=(const pmaybe<t_A> &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    pmaybe<t_A> &operator=(pmaybe<t_A> &&_other) {
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
        return pmaybe<t_A>(PJust{d_a0});
      }
    }

    // CREATORS
    template <typename _U> explicit pmaybe(const pmaybe<_U> &_other) {
      if (std::holds_alternative<typename pmaybe<_U>::PNothing>(_other.v())) {
        d_v_ = PNothing{};
      } else {
        const auto &[d_a0] = std::get<typename pmaybe<_U>::PJust>(_other.v());
        d_v_ = PJust{t_A(d_a0)};
      }
    }

    __attribute__((pure)) static pmaybe<t_A> pnothing() {
      return pmaybe(PNothing{});
    }

    __attribute__((pure)) static pmaybe<t_A> pjust(t_A a0) {
      return pmaybe(PJust{std::move(a0)});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return d_v_; }

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

    ptree<t_A> &operator=(const ptree<t_A> &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    ptree<t_A> &operator=(ptree<t_A> &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) ptree<t_A> clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<PLeaf>(_sv.v())) {
        const auto &[d_a0] = std::get<PLeaf>(_sv.v());
        return ptree<t_A>(PLeaf{d_a0});
      } else {
        const auto &[d_a0, d_a1] = std::get<PNode>(_sv.v());
        return ptree<t_A>(PNode{
            d_a0 ? std::make_unique<PolyInductive::ptree<t_A>>(d_a0->clone())
                 : nullptr,
            d_a1 ? std::make_unique<PolyInductive::ptree<t_A>>(d_a1->clone())
                 : nullptr});
      }
    }

    // CREATORS
    template <typename _U> explicit ptree(const ptree<_U> &_other) {
      if (std::holds_alternative<typename ptree<_U>::PLeaf>(_other.v())) {
        const auto &[d_a0] = std::get<typename ptree<_U>::PLeaf>(_other.v());
        d_v_ = PLeaf{t_A(d_a0)};
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename ptree<_U>::PNode>(_other.v());
        d_v_ = PNode{d_a0 ? std::make_unique<ptree<t_A>>(*d_a0) : nullptr,
                     d_a1 ? std::make_unique<ptree<t_A>>(*d_a1) : nullptr};
      }
    }

    __attribute__((pure)) static ptree<t_A> pleaf(t_A a0) {
      return ptree(PLeaf{std::move(a0)});
    }

    __attribute__((pure)) static ptree<t_A> pnode(const ptree<t_A> &a0,
                                                  const ptree<t_A> &a1) {
      return ptree(PNode{std::make_unique<ptree<t_A>>(a0),
                         std::make_unique<ptree<t_A>>(a1)});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return d_v_; }

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
