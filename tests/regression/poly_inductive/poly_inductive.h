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

    static std::unique_ptr<pbox<t_A>> PBox_uptr(t_A a0) {
      return std::make_unique<pbox<t_A>>(PBox{std::move(a0)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    t_A punbox() const {
      return std::visit(
          Overloaded{[](const typename pbox<t_A>::PBox _args) -> t_A {
            return _args.d_a0;
          }},
          this->v());
    }

    template <typename T1, MapsTo<T1, t_A> F0> T1 pbox_rec(F0 &&f) const {
      return std::visit(
          Overloaded{[&](const typename pbox<t_A>::PBox _args) -> T1 {
            return f(_args.d_a0);
          }},
          this->v());
    }

    template <typename T1, MapsTo<T1, t_A> F0> T1 pbox_rect(F0 &&f) const {
      return std::visit(
          Overloaded{[&](const typename pbox<t_A>::PBox _args) -> T1 {
            return f(_args.d_a0);
          }},
          this->v());
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

    static std::unique_ptr<ppair<t_A, t_B>> PPair_uptr(t_A a0, t_B a1) {
      return std::make_unique<ppair<t_A, t_B>>(
          PPair{std::move(a0), std::move(a1)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    t_B psnd() const {
      return std::visit(
          Overloaded{[](const typename ppair<t_A, t_B>::PPair _args) -> t_B {
            return _args.d_a1;
          }},
          this->v());
    }

    t_A pfst() const {
      return std::visit(
          Overloaded{[](const typename ppair<t_A, t_B>::PPair _args) -> t_A {
            return _args.d_a0;
          }},
          this->v());
    }

    template <typename T1, MapsTo<T1, t_A, t_B> F0> T1 ppair_rec(F0 &&f) const {
      return std::visit(
          Overloaded{[&](const typename ppair<t_A, t_B>::PPair _args) -> T1 {
            return f(_args.d_a0, _args.d_a1);
          }},
          this->v());
    }

    template <typename T1, MapsTo<T1, t_A, t_B> F0>
    T1 ppair_rect(F0 &&f) const {
      return std::visit(
          Overloaded{[&](const typename ppair<t_A, t_B>::PPair _args) -> T1 {
            return f(_args.d_a0, _args.d_a1);
          }},
          this->v());
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
    explicit pmaybe(PNothing _v) : d_v_(std::move(_v)) {}

    explicit pmaybe(PJust _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<pmaybe<t_A>> pnothing() {
      return std::make_shared<pmaybe<t_A>>(PNothing{});
    }

    static std::shared_ptr<pmaybe<t_A>> pjust(t_A a0) {
      return std::make_shared<pmaybe<t_A>>(PJust{std::move(a0)});
    }

    static std::unique_ptr<pmaybe<t_A>> pnothing_uptr() {
      return std::make_unique<pmaybe<t_A>>(PNothing{});
    }

    static std::unique_ptr<pmaybe<t_A>> pjust_uptr(t_A a0) {
      return std::make_unique<pmaybe<t_A>>(PJust{std::move(a0)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    template <typename T1, MapsTo<T1, t_A> F0>
    std::shared_ptr<pmaybe<T1>> pmaybe_map(F0 &&f) const {
      return std::visit(
          Overloaded{[](const typename pmaybe<t_A>::PNothing _args)
                         -> std::shared_ptr<pmaybe<T1>> {
                       return pmaybe<T1>::pnothing();
                     },
                     [&](const typename pmaybe<t_A>::PJust _args)
                         -> std::shared_ptr<pmaybe<T1>> {
                       return pmaybe<T1>::pjust(f(_args.d_a0));
                     }},
          this->v());
    }
  };

  template <typename T1, typename T2, MapsTo<T2, T1> F1>
  static T2 pmaybe_rect(const T2 f, F1 &&f0,
                        const std::shared_ptr<pmaybe<T1>> &p) {
    return std::visit(
        Overloaded{
            [&](const typename pmaybe<T1>::PNothing _args) -> T2 { return f; },
            [&](const typename pmaybe<T1>::PJust _args) -> T2 {
              return f0(_args.d_a0);
            }},
        p->v());
  }

  template <typename T1, typename T2, MapsTo<T2, T1> F1>
  static T2 pmaybe_rec(const T2 f, F1 &&f0,
                       const std::shared_ptr<pmaybe<T1>> &p) {
    return std::visit(
        Overloaded{
            [&](const typename pmaybe<T1>::PNothing _args) -> T2 { return f; },
            [&](const typename pmaybe<T1>::PJust _args) -> T2 {
              return f0(_args.d_a0);
            }},
        p->v());
  }

  template <typename T1>
  static T1 pmaybe_default(const T1 d, const std::shared_ptr<pmaybe<T1>> &m) {
    return std::visit(
        Overloaded{
            [&](const typename pmaybe<T1>::PNothing _args) -> T1 { return d; },
            [](const typename pmaybe<T1>::PJust _args) -> T1 {
              return _args.d_a0;
            }},
        m->v());
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

    static std::unique_ptr<ptree<t_A>> pleaf_uptr(t_A a0) {
      return std::make_unique<ptree<t_A>>(PLeaf{std::move(a0)});
    }

    static std::unique_ptr<ptree<t_A>>
    pnode_uptr(const std::shared_ptr<ptree<t_A>> &a0,
               const std::shared_ptr<ptree<t_A>> &a1) {
      return std::make_unique<ptree<t_A>>(PNode{a0, a1});
    }

    static std::unique_ptr<ptree<t_A>>
    pnode_uptr(std::shared_ptr<ptree<t_A>> &&a0,
               std::shared_ptr<ptree<t_A>> &&a1) {
      return std::make_unique<ptree<t_A>>(PNode{std::move(a0), std::move(a1)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    __attribute__((pure)) unsigned int ptree_size() const {
      return std::visit(
          Overloaded{
              [](const typename ptree<t_A>::PLeaf _args) -> unsigned int {
                return 1u;
              },
              [](const typename ptree<t_A>::PNode _args) -> unsigned int {
                return ((_args.d_a0->ptree_size() + _args.d_a1->ptree_size()) +
                        1);
              }},
          this->v());
    }

    template <typename T1, MapsTo<T1, t_A> F0,
              MapsTo<T1, std::shared_ptr<ptree<t_A>>, T1,
                     std::shared_ptr<ptree<t_A>>, T1>
                  F1>
    T1 ptree_rec(F0 &&f, F1 &&f0) const {
      return std::visit(
          Overloaded{[&](const typename ptree<t_A>::PLeaf _args) -> T1 {
                       return f(_args.d_a0);
                     },
                     [&](const typename ptree<t_A>::PNode _args) -> T1 {
                       return f0(_args.d_a0,
                                 _args.d_a0->template ptree_rec<T1>(f, f0),
                                 _args.d_a1,
                                 _args.d_a1->template ptree_rec<T1>(f, f0));
                     }},
          this->v());
    }

    template <typename T1, MapsTo<T1, t_A> F0,
              MapsTo<T1, std::shared_ptr<ptree<t_A>>, T1,
                     std::shared_ptr<ptree<t_A>>, T1>
                  F1>
    T1 ptree_rect(F0 &&f, F1 &&f0) const {
      return std::visit(
          Overloaded{[&](const typename ptree<t_A>::PLeaf _args) -> T1 {
                       return f(_args.d_a0);
                     },
                     [&](const typename ptree<t_A>::PNode _args) -> T1 {
                       return f0(_args.d_a0,
                                 _args.d_a0->template ptree_rect<T1>(f, f0),
                                 _args.d_a1,
                                 _args.d_a1->template ptree_rect<T1>(f, f0));
                     }},
          this->v());
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
              [](unsigned int x) { return (x + 1); }));
  static inline const unsigned int test_ptree =
      ptree<unsigned int>::pnode(
          ptree<unsigned int>::pleaf(1u),
          ptree<unsigned int>::pnode(ptree<unsigned int>::pleaf(2u),
                                     ptree<unsigned int>::pleaf(3u)))
          ->ptree_size();
};

#endif // INCLUDED_POLY_INDUCTIVE
