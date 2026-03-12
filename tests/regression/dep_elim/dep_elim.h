#ifndef INCLUDED_DEP_ELIM
#define INCLUDED_DEP_ELIM

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

template <typename A> struct List {
  // TYPES
  struct nil {};

  struct cons {
    A _a0;
    std::shared_ptr<List<A>> _a1;
  };

  using variant_t = std::variant<nil, cons>;

private:
  // DATA
  variant_t v_;

  // CREATORS
  explicit List(nil _v) : v_(std::move(_v)) {}

  explicit List(cons _v) : v_(std::move(_v)) {}

public:
  // TYPES
  struct ctor {
    ctor() = delete;

    static std::shared_ptr<List<A>> nil_() {
      return std::shared_ptr<List<A>>(new List<A>(nil{}));
    }

    static std::shared_ptr<List<A>> cons_(A a0,
                                          const std::shared_ptr<List<A>> &a1) {
      return std::shared_ptr<List<A>>(new List<A>(cons{a0, a1}));
    }

    static std::unique_ptr<List<A>> nil_uptr() {
      return std::unique_ptr<List<A>>(new List<A>(nil{}));
    }

    static std::unique_ptr<List<A>>
    cons_uptr(A a0, const std::shared_ptr<List<A>> &a1) {
      return std::unique_ptr<List<A>>(new List<A>(cons{a0, a1}));
    }
  };

  // MANIPULATORS
  variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct DepElim {
  struct fin {
    // TYPES
    struct FZ {
      unsigned int _a0;
    };

    struct FS {
      unsigned int _a0;
      std::shared_ptr<fin> _a1;
    };

    using variant_t = std::variant<FZ, FS>;

  private:
    // DATA
    variant_t v_;

    // CREATORS
    explicit fin(FZ _v) : v_(std::move(_v)) {}

    explicit fin(FS _v) : v_(std::move(_v)) {}

  public:
    // TYPES
    struct ctor {
      ctor() = delete;

      static std::shared_ptr<fin> FZ_(unsigned int a0) {
        return std::shared_ptr<fin>(new fin(FZ{a0}));
      }

      static std::shared_ptr<fin> FS_(unsigned int a0,
                                      const std::shared_ptr<fin> &a1) {
        return std::shared_ptr<fin>(new fin(FS{a0, a1}));
      }

      static std::unique_ptr<fin> FZ_uptr(unsigned int a0) {
        return std::unique_ptr<fin>(new fin(FZ{a0}));
      }

      static std::unique_ptr<fin> FS_uptr(unsigned int a0,
                                          const std::shared_ptr<fin> &a1) {
        return std::unique_ptr<fin>(new fin(FS{a0, a1}));
      }
    };

    // MANIPULATORS
    variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, MapsTo<T1, unsigned int> F0,
            MapsTo<T1, unsigned int, std::shared_ptr<fin>, T1> F1>
  static T1 fin_rect(F0 &&f, F1 &&f0, const unsigned int _x,
                     const std::shared_ptr<fin> &f1) {
    return std::visit(Overloaded{[&](const typename fin::FZ _args) -> T1 {
                                   unsigned int n = _args._a0;
                                   return f(std::move(n));
                                 },
                                 [&](const typename fin::FS _args) -> T1 {
                                   unsigned int n = _args._a0;
                                   std::shared_ptr<fin> f2 = _args._a1;
                                   return f0(n, f2, fin_rect<T1>(f, f0, n, f2));
                                 }},
                      f1->v());
  }

  template <typename T1, MapsTo<T1, unsigned int> F0,
            MapsTo<T1, unsigned int, std::shared_ptr<fin>, T1> F1>
  static T1 fin_rec(F0 &&f, F1 &&f0, const unsigned int _x,
                    const std::shared_ptr<fin> &f1) {
    return std::visit(Overloaded{[&](const typename fin::FZ _args) -> T1 {
                                   unsigned int n = _args._a0;
                                   return f(std::move(n));
                                 },
                                 [&](const typename fin::FS _args) -> T1 {
                                   unsigned int n = _args._a0;
                                   std::shared_ptr<fin> f2 = _args._a1;
                                   return f0(n, f2, fin_rec<T1>(f, f0, n, f2));
                                 }},
                      f1->v());
  }

  static unsigned int fin_to_nat(const unsigned int _x,
                                 const std::shared_ptr<fin> &f);

  template <typename A> struct vec {
    // TYPES
    struct vnil {};

    struct vcons {
      unsigned int _a0;
      A _a1;
      std::shared_ptr<vec<A>> _a2;
    };

    using variant_t = std::variant<vnil, vcons>;

  private:
    // DATA
    variant_t v_;

    // CREATORS
    explicit vec(vnil _v) : v_(std::move(_v)) {}

    explicit vec(vcons _v) : v_(std::move(_v)) {}

  public:
    // TYPES
    struct ctor {
      ctor() = delete;

      static std::shared_ptr<vec<A>> vnil_() {
        return std::shared_ptr<vec<A>>(new vec<A>(vnil{}));
      }

      static std::shared_ptr<vec<A>> vcons_(unsigned int a0, A a1,
                                            const std::shared_ptr<vec<A>> &a2) {
        return std::shared_ptr<vec<A>>(new vec<A>(vcons{a0, a1, a2}));
      }

      static std::unique_ptr<vec<A>> vnil_uptr() {
        return std::unique_ptr<vec<A>>(new vec<A>(vnil{}));
      }

      static std::unique_ptr<vec<A>>
      vcons_uptr(unsigned int a0, A a1, const std::shared_ptr<vec<A>> &a2) {
        return std::unique_ptr<vec<A>>(new vec<A>(vcons{a0, a1, a2}));
      }
    };

    // MANIPULATORS
    variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename T2,
            MapsTo<T2, unsigned int, T1, std::shared_ptr<vec<T1>>, T2> F1>
  static T2 vec_rect(const T2 f, F1 &&f0, const unsigned int _x,
                     const std::shared_ptr<vec<T1>> &v) {
    return std::visit(
        Overloaded{[&](const typename vec<T1>::vnil _args) -> T2 { return f; },
                   [&](const typename vec<T1>::vcons _args) -> T2 {
                     unsigned int n = _args._a0;
                     T1 y = _args._a1;
                     std::shared_ptr<vec<T1>> v0 = _args._a2;
                     return f0(n, y, v0, vec_rect<T1, T2>(f, f0, n, v0));
                   }},
        v->v());
  }

  template <typename T1, typename T2,
            MapsTo<T2, unsigned int, T1, std::shared_ptr<vec<T1>>, T2> F1>
  static T2 vec_rec(const T2 f, F1 &&f0, const unsigned int _x,
                    const std::shared_ptr<vec<T1>> &v) {
    return std::visit(
        Overloaded{[&](const typename vec<T1>::vnil _args) -> T2 { return f; },
                   [&](const typename vec<T1>::vcons _args) -> T2 {
                     unsigned int n = _args._a0;
                     T1 y = _args._a1;
                     std::shared_ptr<vec<T1>> v0 = _args._a2;
                     return f0(n, y, v0, vec_rec<T1, T2>(f, f0, n, v0));
                   }},
        v->v());
  }

  template <typename T1>
  static std::shared_ptr<List<T1>>
  vec_to_list(const unsigned int _x, const std::shared_ptr<vec<T1>> &v) {
    return std::visit(
        Overloaded{
            [](const typename vec<T1>::vnil _args)
                -> std::shared_ptr<List<T1>> { return List<T1>::ctor::nil_(); },
            [](const typename vec<T1>::vcons _args)
                -> std::shared_ptr<List<T1>> {
              unsigned int n0 = _args._a0;
              T1 x = _args._a1;
              std::shared_ptr<vec<T1>> xs = _args._a2;
              return List<T1>::ctor::cons_(
                  x, vec_to_list<T1>(std::move(n0), std::move(xs)));
            }},
        v->v());
  }

  template <typename T1, typename T2, MapsTo<T2, T1> F1>
  static std::shared_ptr<vec<T2>> vec_map(const unsigned int _x, F1 &&f,
                                          const std::shared_ptr<vec<T1>> &v) {
    return std::visit(
        Overloaded{
            [](const typename vec<T1>::vnil _args) -> std::shared_ptr<vec<T2>> {
              return vec<T2>::ctor::vnil_();
            },
            [&](const typename vec<T1>::vcons _args)
                -> std::shared_ptr<vec<T2>> {
              unsigned int n0 = _args._a0;
              T1 x = _args._a1;
              std::shared_ptr<vec<T1>> xs = _args._a2;
              return vec<T2>::ctor::vcons_(
                  n0, f(x), vec_map<T1, T2>(n0, f, std::move(xs)));
            }},
        v->v());
  }

  template <typename T1>
  static T1 vec_head(const unsigned int _x, const std::shared_ptr<vec<T1>> &v) {
    return std::visit(Overloaded{[](const typename vec<T1>::vnil _args) -> T1 {
                                   throw std::logic_error("unreachable");
                                 },
                                 [](const typename vec<T1>::vcons _args) -> T1 {
                                   T1 x = _args._a1;
                                   return x;
                                 }},
                      v->v());
  }

  template <typename T1>
  static std::shared_ptr<vec<T1>> vec_tail(const unsigned int _x,
                                           const std::shared_ptr<vec<T1>> &v) {
    return std::visit(
        Overloaded{
            [](const typename vec<T1>::vnil _args) -> std::shared_ptr<vec<T1>> {
              throw std::logic_error("unreachable");
            },
            [](const typename vec<T1>::vcons _args)
                -> std::shared_ptr<vec<T1>> {
              std::shared_ptr<vec<T1>> xs = _args._a2;
              return std::move(xs);
            }},
        v->v());
  }

  struct avail {
    // TYPES
    struct present {
      unsigned int _a0;
    };

    struct absent {};

    using variant_t = std::variant<present, absent>;

  private:
    // DATA
    variant_t v_;

    // CREATORS
    explicit avail(present _v) : v_(std::move(_v)) {}

    explicit avail(absent _v) : v_(std::move(_v)) {}

  public:
    // TYPES
    struct ctor {
      ctor() = delete;

      static std::shared_ptr<avail> present_(unsigned int a0) {
        return std::shared_ptr<avail>(new avail(present{a0}));
      }

      static std::shared_ptr<avail> absent_() {
        return std::shared_ptr<avail>(new avail(absent{}));
      }

      static std::unique_ptr<avail> present_uptr(unsigned int a0) {
        return std::unique_ptr<avail>(new avail(present{a0}));
      }

      static std::unique_ptr<avail> absent_uptr() {
        return std::unique_ptr<avail>(new avail(absent{}));
      }
    };

    // MANIPULATORS
    variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, MapsTo<T1, unsigned int> F0>
  static T1 avail_rect(F0 &&f, const T1 f0, const bool _x,
                       const std::shared_ptr<avail> &a) {
    return std::visit(
        Overloaded{
            [&](const typename avail::present _args) -> T1 {
              unsigned int n = _args._a0;
              return f(std::move(n));
            },
            [&](const typename avail::absent _args) -> T1 { return f0; }},
        a->v());
  }

  template <typename T1, MapsTo<T1, unsigned int> F0>
  static T1 avail_rec(F0 &&f, const T1 f0, const bool _x,
                      const std::shared_ptr<avail> &a) {
    return std::visit(
        Overloaded{
            [&](const typename avail::present _args) -> T1 {
              unsigned int n = _args._a0;
              return f(std::move(n));
            },
            [&](const typename avail::absent _args) -> T1 { return f0; }},
        a->v());
  }

  static unsigned int get_present(const std::shared_ptr<avail> &a);
  static inline const unsigned int test_fin0 =
      fin_to_nat(3u, fin::ctor::FZ_(2u));
  static inline const unsigned int test_fin2 = fin_to_nat(
      3u, fin::ctor::FS_(2u, fin::ctor::FS_(1u, fin::ctor::FZ_(0u))));
  static inline const std::shared_ptr<vec<unsigned int>> my_vec =
      vec<unsigned int>::ctor::vcons_(
          2u, 10u,
          vec<unsigned int>::ctor::vcons_(
              1u, 20u,
              vec<unsigned int>::ctor::vcons_(
                  0u, 30u, vec<unsigned int>::ctor::vnil_())));
  static inline const std::shared_ptr<List<unsigned int>> test_vec_list =
      vec_to_list<unsigned int>(3u, my_vec);
  static inline const unsigned int test_vec_head =
      vec_head<unsigned int>(2u, my_vec);
  static inline const std::shared_ptr<List<unsigned int>> test_vec_tail_list =
      vec_to_list<unsigned int>(2u, vec_tail<unsigned int>(2u, my_vec));
  static inline const std::shared_ptr<List<unsigned int>> test_vec_map =
      vec_to_list<unsigned int>(
          3u, vec_map<unsigned int, unsigned int>(
                  3u, [](unsigned int n) { return (n + 1u); }, my_vec));
  static inline const unsigned int test_present =
      get_present(avail::ctor::present_(42u));
};

#endif // INCLUDED_DEP_ELIM
