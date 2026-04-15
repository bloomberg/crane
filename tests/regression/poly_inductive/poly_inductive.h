#ifndef INCLUDED_POLY_INDUCTIVE
#define INCLUDED_POLY_INDUCTIVE

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

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
    explicit pbox(PBox _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<pbox<t_A>> PBox_(t_A a0) {
      return std::make_shared<pbox<t_A>>(PBox{std::move(a0)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    t_A punbox() const {
      const auto &_m = *std::get_if<typename pbox<t_A>::PBox>(&this->v());
      return _m.d_a0;
    }

    template <typename T1, MapsTo<T1, t_A> F0> T1 pbox_rec(F0 &&f) const {
      const auto &_m = *std::get_if<typename pbox<t_A>::PBox>(&this->v());
      return f(_m.d_a0);
    }

    template <typename T1, MapsTo<T1, t_A> F0> T1 pbox_rect(F0 &&f) const {
      const auto &_m = *std::get_if<typename pbox<t_A>::PBox>(&this->v());
      return f(_m.d_a0);
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
    explicit ppair(PPair _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<ppair<t_A, t_B>> PPair_(t_A a0, t_B a1) {
      return std::make_shared<ppair<t_A, t_B>>(
          PPair{std::move(a0), std::move(a1)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    t_B psnd() const {
      const auto &_m =
          *std::get_if<typename ppair<t_A, t_B>::PPair>(&this->v());
      return _m.d_a1;
    }

    t_A pfst() const {
      const auto &_m =
          *std::get_if<typename ppair<t_A, t_B>::PPair>(&this->v());
      return _m.d_a0;
    }

    template <typename T1, MapsTo<T1, t_A, t_B> F0> T1 ppair_rec(F0 &&f) const {
      const auto &_m =
          *std::get_if<typename ppair<t_A, t_B>::PPair>(&this->v());
      return f(_m.d_a0, _m.d_a1);
    }

    template <typename T1, MapsTo<T1, t_A, t_B> F0>
    T1 ppair_rect(F0 &&f) const {
      const auto &_m =
          *std::get_if<typename ppair<t_A, t_B>::PPair>(&this->v());
      return f(_m.d_a0, _m.d_a1);
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
    explicit pmaybe(PNothing _v) : d_v_(_v) {}

    explicit pmaybe(PJust _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<pmaybe<t_A>> pnothing() {
      return std::make_shared<pmaybe<t_A>>(PNothing{});
    }

    static std::shared_ptr<pmaybe<t_A>> pjust(t_A a0) {
      return std::make_shared<pmaybe<t_A>>(PJust{std::move(a0)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    template <typename T1, MapsTo<T1, t_A> F0>
    std::shared_ptr<pmaybe<T1>> pmaybe_map(F0 &&f) const {
      if (std::holds_alternative<typename pmaybe<t_A>::PNothing>(this->v())) {
        return pmaybe<T1>::pnothing();
      } else {
        const auto &_m = *std::get_if<typename pmaybe<t_A>::PJust>(&this->v());
        return pmaybe<T1>::pjust(f(_m.d_a0));
      }
    }
  };

  template <typename T1, typename T2, MapsTo<T2, T1> F1>
  static T2 pmaybe_rect(const T2 f, F1 &&f0,
                        const std::shared_ptr<pmaybe<T1>> &p) {
    if (std::holds_alternative<typename pmaybe<T1>::PNothing>(p->v())) {
      return f;
    } else {
      const auto &_m = *std::get_if<typename pmaybe<T1>::PJust>(&p->v());
      return f0(_m.d_a0);
    }
  }

  template <typename T1, typename T2, MapsTo<T2, T1> F1>
  static T2 pmaybe_rec(const T2 f, F1 &&f0,
                       const std::shared_ptr<pmaybe<T1>> &p) {
    if (std::holds_alternative<typename pmaybe<T1>::PNothing>(p->v())) {
      return f;
    } else {
      const auto &_m = *std::get_if<typename pmaybe<T1>::PJust>(&p->v());
      return f0(_m.d_a0);
    }
  }

  template <typename T1>
  static T1 pmaybe_default(const T1 d, const std::shared_ptr<pmaybe<T1>> &m) {
    if (std::holds_alternative<typename pmaybe<T1>::PNothing>(m->v())) {
      return d;
    } else {
      const auto &_m = *std::get_if<typename pmaybe<T1>::PJust>(&m->v());
      return _m.d_a0;
    }
  }

  template <typename t_A> struct ptree {
    // TYPES
    struct PLeaf {
      t_A d_a0;
    };

    struct PNode {
      std::shared_ptr<ptree<t_A>> d_a0;
      std::shared_ptr<ptree<t_A>> d_a1;
    };

    using variant_t = std::variant<PLeaf, PNode>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    explicit ptree(PLeaf _v) : d_v_(std::move(_v)) {}

    explicit ptree(PNode _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<ptree<t_A>> pleaf(t_A a0) {
      return std::make_shared<ptree<t_A>>(PLeaf{std::move(a0)});
    }

    static std::shared_ptr<ptree<t_A>>
    pnode(const std::shared_ptr<ptree<t_A>> &a0,
          const std::shared_ptr<ptree<t_A>> &a1) {
      return std::make_shared<ptree<t_A>>(PNode{a0, a1});
    }

    static std::shared_ptr<ptree<t_A>> pnode(std::shared_ptr<ptree<t_A>> &&a0,
                                             std::shared_ptr<ptree<t_A>> &&a1) {
      return std::make_shared<ptree<t_A>>(PNode{std::move(a0), std::move(a1)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    __attribute__((pure)) unsigned int ptree_size() const {
      if (std::holds_alternative<typename ptree<t_A>::PLeaf>(this->v())) {
        return 1u;
      } else {
        const auto &_m = *std::get_if<typename ptree<t_A>::PNode>(&this->v());
        return ((_m.d_a0->ptree_size() + _m.d_a1->ptree_size()) + 1);
      }
    }

    template <typename T1, MapsTo<T1, t_A> F0,
              MapsTo<T1, std::shared_ptr<ptree<t_A>>, T1,
                     std::shared_ptr<ptree<t_A>>, T1>
                  F1>
    T1 ptree_rec(F0 &&f, F1 &&f0) const {
      if (std::holds_alternative<typename ptree<t_A>::PLeaf>(this->v())) {
        const auto &_m = *std::get_if<typename ptree<t_A>::PLeaf>(&this->v());
        return f(_m.d_a0);
      } else {
        const auto &_m = *std::get_if<typename ptree<t_A>::PNode>(&this->v());
        return f0(_m.d_a0, _m.d_a0->template ptree_rec<T1>(f, f0), _m.d_a1,
                  _m.d_a1->template ptree_rec<T1>(f, f0));
      }
    }

    template <typename T1, MapsTo<T1, t_A> F0,
              MapsTo<T1, std::shared_ptr<ptree<t_A>>, T1,
                     std::shared_ptr<ptree<t_A>>, T1>
                  F1>
    T1 ptree_rect(F0 &&f, F1 &&f0) const {
      if (std::holds_alternative<typename ptree<t_A>::PLeaf>(this->v())) {
        const auto &_m = *std::get_if<typename ptree<t_A>::PLeaf>(&this->v());
        return f(_m.d_a0);
      } else {
        const auto &_m = *std::get_if<typename ptree<t_A>::PNode>(&this->v());
        return f0(_m.d_a0, _m.d_a0->template ptree_rect<T1>(f, f0), _m.d_a1,
                  _m.d_a1->template ptree_rect<T1>(f, f0));
      }
    }
  };

  static inline const unsigned int test_pbox =
      pbox<unsigned int>::PBox_(42u)->punbox();
  static inline const unsigned int test_ppair_fst =
      ppair<unsigned int, bool>::PPair_(7u, true)->pfst();
  static inline const bool test_ppair_snd =
      ppair<unsigned int, bool>::PPair_(7u, true)->psnd();
  static inline const unsigned int test_pjust =
      pmaybe_default<unsigned int>(0u, pmaybe<unsigned int>::pjust(99u));
  static inline const unsigned int test_pnothing =
      pmaybe_default<unsigned int>(0u, pmaybe<unsigned int>::pnothing());
  static inline const unsigned int test_pmap = pmaybe_default<unsigned int>(
      0u, pmaybe<unsigned int>::pjust(5u)->template pmaybe_map<unsigned int>(
              [](const unsigned int x) { return (x + 1); }));
  static inline const unsigned int test_ptree =
      ptree<unsigned int>::pnode(
          ptree<unsigned int>::pleaf(1u),
          ptree<unsigned int>::pnode(ptree<unsigned int>::pleaf(2u),
                                     ptree<unsigned int>::pleaf(3u)))
          ->ptree_size();
};

#endif // INCLUDED_POLY_INDUCTIVE
