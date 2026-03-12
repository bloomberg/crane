#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

struct PolyInductive {
  template <typename A> struct pbox {
    // TYPES
    struct PBox {
      A _a0;
    };

    using variant_t = std::variant<PBox>;

  private:
    // DATA
    variant_t v_;

    // CREATORS
    explicit pbox(PBox _v) : v_(std::move(_v)) {}

  public:
    // TYPES
    struct ctor {
      ctor() = delete;

      static std::shared_ptr<pbox<A>> PBox_(A a0) {
        return std::shared_ptr<pbox<A>>(new pbox<A>(PBox{a0}));
      }

      static std::unique_ptr<pbox<A>> PBox_uptr(A a0) {
        return std::unique_ptr<pbox<A>>(new pbox<A>(PBox{a0}));
      }
    };

    // MANIPULATORS
    variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename T2, MapsTo<T2, T1> F0>
  static T2 pbox_rect(F0 &&f, const std::shared_ptr<pbox<T1>> &p) {
    return std::visit(
        Overloaded{[&](const typename pbox<T1>::PBox _args) -> T2 {
          T1 a = _args._a0;
          return f(a);
        }},
        p->v());
  }

  template <typename T1, typename T2, MapsTo<T2, T1> F0>
  static T2 pbox_rec(F0 &&f, const std::shared_ptr<pbox<T1>> &p) {
    return std::visit(
        Overloaded{[&](const typename pbox<T1>::PBox _args) -> T2 {
          T1 a = _args._a0;
          return f(a);
        }},
        p->v());
  }

  template <typename T1> static T1 punbox(const std::shared_ptr<pbox<T1>> &b) {
    return std::visit(Overloaded{[](const typename pbox<T1>::PBox _args) -> T1 {
                        T1 x = _args._a0;
                        return x;
                      }},
                      b->v());
  }

  template <typename A, typename B> struct ppair {
    // TYPES
    struct PPair {
      A _a0;
      B _a1;
    };

    using variant_t = std::variant<PPair>;

  private:
    // DATA
    variant_t v_;

    // CREATORS
    explicit ppair(PPair _v) : v_(std::move(_v)) {}

  public:
    // TYPES
    struct ctor {
      ctor() = delete;

      static std::shared_ptr<ppair<A, B>> PPair_(A a0, B a1) {
        return std::shared_ptr<ppair<A, B>>(new ppair<A, B>(PPair{a0, a1}));
      }

      static std::unique_ptr<ppair<A, B>> PPair_uptr(A a0, B a1) {
        return std::unique_ptr<ppair<A, B>>(new ppair<A, B>(PPair{a0, a1}));
      }
    };

    // MANIPULATORS
    variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename T2, typename T3, MapsTo<T3, T1, T2> F0>
  static T3 ppair_rect(F0 &&f, const std::shared_ptr<ppair<T1, T2>> &p) {
    return std::visit(
        Overloaded{[&](const typename ppair<T1, T2>::PPair _args) -> T3 {
          T1 a = _args._a0;
          T2 b = _args._a1;
          return f(a, b);
        }},
        p->v());
  }

  template <typename T1, typename T2, typename T3, MapsTo<T3, T1, T2> F0>
  static T3 ppair_rec(F0 &&f, const std::shared_ptr<ppair<T1, T2>> &p) {
    return std::visit(
        Overloaded{[&](const typename ppair<T1, T2>::PPair _args) -> T3 {
          T1 a = _args._a0;
          T2 b = _args._a1;
          return f(a, b);
        }},
        p->v());
  }

  template <typename T1, typename T2>
  static T1 pfst(const std::shared_ptr<ppair<T1, T2>> &p) {
    return std::visit(
        Overloaded{[](const typename ppair<T1, T2>::PPair _args) -> T1 {
          T1 a = _args._a0;
          return a;
        }},
        p->v());
  }

  template <typename T1, typename T2>
  static T2 psnd(const std::shared_ptr<ppair<T1, T2>> &p) {
    return std::visit(
        Overloaded{[](const typename ppair<T1, T2>::PPair _args) -> T2 {
          T2 b = _args._a1;
          return b;
        }},
        p->v());
  }

  template <typename A> struct pmaybe {
    // TYPES
    struct PNothing {};

    struct PJust {
      A _a0;
    };

    using variant_t = std::variant<PNothing, PJust>;

  private:
    // DATA
    variant_t v_;

    // CREATORS
    explicit pmaybe(PNothing _v) : v_(std::move(_v)) {}

    explicit pmaybe(PJust _v) : v_(std::move(_v)) {}

  public:
    // TYPES
    struct ctor {
      ctor() = delete;

      static std::shared_ptr<pmaybe<A>> PNothing_() {
        return std::shared_ptr<pmaybe<A>>(new pmaybe<A>(PNothing{}));
      }

      static std::shared_ptr<pmaybe<A>> PJust_(A a0) {
        return std::shared_ptr<pmaybe<A>>(new pmaybe<A>(PJust{a0}));
      }

      static std::unique_ptr<pmaybe<A>> PNothing_uptr() {
        return std::unique_ptr<pmaybe<A>>(new pmaybe<A>(PNothing{}));
      }

      static std::unique_ptr<pmaybe<A>> PJust_uptr(A a0) {
        return std::unique_ptr<pmaybe<A>>(new pmaybe<A>(PJust{a0}));
      }
    };

    // MANIPULATORS
    variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename T2, MapsTo<T2, T1> F1>
  static T2 pmaybe_rect(const T2 f, F1 &&f0,
                        const std::shared_ptr<pmaybe<T1>> &p) {
    return std::visit(
        Overloaded{
            [&](const typename pmaybe<T1>::PNothing _args) -> T2 { return f; },
            [&](const typename pmaybe<T1>::PJust _args) -> T2 {
              T1 a = _args._a0;
              return f0(a);
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
              T1 a = _args._a0;
              return f0(a);
            }},
        p->v());
  }

  template <typename T1, typename T2, MapsTo<T2, T1> F0>
  static std::shared_ptr<pmaybe<T2>>
  pmaybe_map(F0 &&f, const std::shared_ptr<pmaybe<T1>> &m) {
    return std::visit(Overloaded{[](const typename pmaybe<T1>::PNothing _args)
                                     -> std::shared_ptr<pmaybe<T2>> {
                                   return pmaybe<T2>::ctor::PNothing_();
                                 },
                                 [&](const typename pmaybe<T1>::PJust _args)
                                     -> std::shared_ptr<pmaybe<T2>> {
                                   T1 x = _args._a0;
                                   return pmaybe<T2>::ctor::PJust_(f(x));
                                 }},
                      m->v());
  }

  template <typename T1>
  static T1 pmaybe_default(const T1 d, const std::shared_ptr<pmaybe<T1>> &m) {
    return std::visit(
        Overloaded{
            [&](const typename pmaybe<T1>::PNothing _args) -> T1 { return d; },
            [](const typename pmaybe<T1>::PJust _args) -> T1 {
              T1 x = _args._a0;
              return x;
            }},
        m->v());
  }

  template <typename A> struct ptree {
    // TYPES
    struct PLeaf {
      A _a0;
    };

    struct PNode {
      std::shared_ptr<ptree<A>> _a0;
      std::shared_ptr<ptree<A>> _a1;
    };

    using variant_t = std::variant<PLeaf, PNode>;

  private:
    // DATA
    variant_t v_;

    // CREATORS
    explicit ptree(PLeaf _v) : v_(std::move(_v)) {}

    explicit ptree(PNode _v) : v_(std::move(_v)) {}

  public:
    // TYPES
    struct ctor {
      ctor() = delete;

      static std::shared_ptr<ptree<A>> PLeaf_(A a0) {
        return std::shared_ptr<ptree<A>>(new ptree<A>(PLeaf{a0}));
      }

      static std::shared_ptr<ptree<A>>
      PNode_(const std::shared_ptr<ptree<A>> &a0,
             const std::shared_ptr<ptree<A>> &a1) {
        return std::shared_ptr<ptree<A>>(new ptree<A>(PNode{a0, a1}));
      }

      static std::unique_ptr<ptree<A>> PLeaf_uptr(A a0) {
        return std::unique_ptr<ptree<A>>(new ptree<A>(PLeaf{a0}));
      }

      static std::unique_ptr<ptree<A>>
      PNode_uptr(const std::shared_ptr<ptree<A>> &a0,
                 const std::shared_ptr<ptree<A>> &a1) {
        return std::unique_ptr<ptree<A>>(new ptree<A>(PNode{a0, a1}));
      }
    };

    // MANIPULATORS
    variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <
      typename T1, typename T2, MapsTo<T2, T1> F0,
      MapsTo<T2, std::shared_ptr<ptree<T1>>, T2, std::shared_ptr<ptree<T1>>, T2>
          F1>
  static T2 ptree_rect(F0 &&f, F1 &&f0, const std::shared_ptr<ptree<T1>> &p) {
    return std::visit(
        Overloaded{[&](const typename ptree<T1>::PLeaf _args) -> T2 {
                     T1 y = _args._a0;
                     return f(y);
                   },
                   [&](const typename ptree<T1>::PNode _args) -> T2 {
                     std::shared_ptr<ptree<T1>> p0 = _args._a0;
                     std::shared_ptr<ptree<T1>> p1 = _args._a1;
                     return f0(p0, ptree_rect<T1, T2>(f, f0, p0), p1,
                               ptree_rect<T1, T2>(f, f0, p1));
                   }},
        p->v());
  }

  template <
      typename T1, typename T2, MapsTo<T2, T1> F0,
      MapsTo<T2, std::shared_ptr<ptree<T1>>, T2, std::shared_ptr<ptree<T1>>, T2>
          F1>
  static T2 ptree_rec(F0 &&f, F1 &&f0, const std::shared_ptr<ptree<T1>> &p) {
    return std::visit(
        Overloaded{[&](const typename ptree<T1>::PLeaf _args) -> T2 {
                     T1 y = _args._a0;
                     return f(y);
                   },
                   [&](const typename ptree<T1>::PNode _args) -> T2 {
                     std::shared_ptr<ptree<T1>> p0 = _args._a0;
                     std::shared_ptr<ptree<T1>> p1 = _args._a1;
                     return f0(p0, ptree_rec<T1, T2>(f, f0, p0), p1,
                               ptree_rec<T1, T2>(f, f0, p1));
                   }},
        p->v());
  }

  template <typename T1>
  static unsigned int ptree_size(const std::shared_ptr<ptree<T1>> &t) {
    return std::visit(
        Overloaded{[](const typename ptree<T1>::PLeaf _args) -> unsigned int {
                     return 1u;
                   },
                   [](const typename ptree<T1>::PNode _args) -> unsigned int {
                     std::shared_ptr<ptree<T1>> l = _args._a0;
                     std::shared_ptr<ptree<T1>> r = _args._a1;
                     return ((ptree_size<T1>(std::move(l)) +
                              ptree_size<T1>(std::move(r))) +
                             1);
                   }},
        t->v());
  }

  static inline const unsigned int test_pbox =
      punbox<unsigned int>(pbox<unsigned int>::ctor::PBox_(42u));
  static inline const unsigned int test_ppair_fst = pfst<unsigned int, bool>(
      ppair<unsigned int, bool>::ctor::PPair_(7u, true));
  static inline const bool test_ppair_snd = psnd<unsigned int, bool>(
      ppair<unsigned int, bool>::ctor::PPair_(7u, true));
  static inline const unsigned int test_pjust =
      pmaybe_default<unsigned int>(0u, pmaybe<unsigned int>::ctor::PJust_(99u));
  static inline const unsigned int test_pnothing =
      pmaybe_default<unsigned int>(0u, pmaybe<unsigned int>::ctor::PNothing_());
  static inline const unsigned int test_pmap = pmaybe_default<unsigned int>(
      0u, pmaybe_map<unsigned int, unsigned int>(
              [](unsigned int x) { return (x + 1); },
              pmaybe<unsigned int>::ctor::PJust_(5u)));
  static inline const unsigned int test_ptree =
      ptree_size<unsigned int>(ptree<unsigned int>::ctor::PNode_(
          ptree<unsigned int>::ctor::PLeaf_(1u),
          ptree<unsigned int>::ctor::PNode_(
              ptree<unsigned int>::ctor::PLeaf_(2u),
              ptree<unsigned int>::ctor::PLeaf_(3u))));
};
