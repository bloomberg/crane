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

template <typename t_A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    t_A d_a0;
    std::shared_ptr<List<t_A>> d_a1;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t d_v_;

  // CREATORS
  explicit List(Nil _v) : d_v_(std::move(_v)) {}

  explicit List(Cons _v) : d_v_(std::move(_v)) {}

public:
  // TYPES
  struct ctor {
    ctor() = delete;

    static std::shared_ptr<List<t_A>> Nil_() {
      return std::shared_ptr<List<t_A>>(new List<t_A>(Nil{}));
    }

    static std::shared_ptr<List<t_A>>
    Cons_(t_A a0, const std::shared_ptr<List<t_A>> &a1) {
      return std::shared_ptr<List<t_A>>(new List<t_A>(Cons{a0, a1}));
    }

    static std::unique_ptr<List<t_A>> Nil_uptr() {
      return std::unique_ptr<List<t_A>>(new List<t_A>(Nil{}));
    }

    static std::unique_ptr<List<t_A>>
    Cons_uptr(t_A a0, const std::shared_ptr<List<t_A>> &a1) {
      return std::unique_ptr<List<t_A>>(new List<t_A>(Cons{a0, a1}));
    }
  };

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
};

struct DepElim {
  struct fin {
    // TYPES
    struct FZ {
      unsigned int d_a0;
    };

    struct FS {
      unsigned int d_a0;
      std::shared_ptr<fin> d_a1;
    };

    using variant_t = std::variant<FZ, FS>;

  private:
    // DATA
    variant_t d_v_;

    // CREATORS
    explicit fin(FZ _v) : d_v_(std::move(_v)) {}

    explicit fin(FS _v) : d_v_(std::move(_v)) {}

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
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, unsigned int> F0,
            MapsTo<T1, unsigned int, std::shared_ptr<fin>, T1> F1>
  static T1 fin_rect(F0 &&f, F1 &&f0, const unsigned int _x,
                     const std::shared_ptr<fin> &f1) {
    return std::visit(Overloaded{[&](const typename fin::FZ _args) -> T1 {
                                   unsigned int n = _args.d_a0;
                                   return f(std::move(n));
                                 },
                                 [&](const typename fin::FS _args) -> T1 {
                                   unsigned int n = _args.d_a0;
                                   std::shared_ptr<fin> f2 = _args.d_a1;
                                   return f0(n, f2, fin_rect<T1>(f, f0, n, f2));
                                 }},
                      f1->v());
  }

  template <typename T1, MapsTo<T1, unsigned int> F0,
            MapsTo<T1, unsigned int, std::shared_ptr<fin>, T1> F1>
  static T1 fin_rec(F0 &&f, F1 &&f0, const unsigned int _x,
                    const std::shared_ptr<fin> &f1) {
    return std::visit(Overloaded{[&](const typename fin::FZ _args) -> T1 {
                                   unsigned int n = _args.d_a0;
                                   return f(std::move(n));
                                 },
                                 [&](const typename fin::FS _args) -> T1 {
                                   unsigned int n = _args.d_a0;
                                   std::shared_ptr<fin> f2 = _args.d_a1;
                                   return f0(n, f2, fin_rec<T1>(f, f0, n, f2));
                                 }},
                      f1->v());
  }

  __attribute__((pure)) static unsigned int
  fin_to_nat(const unsigned int _x, const std::shared_ptr<fin> &f);

  template <typename t_A> struct vec {
    // TYPES
    struct Vnil {};

    struct Vcons {
      unsigned int d_a0;
      t_A d_a1;
      std::shared_ptr<vec<t_A>> d_a2;
    };

    using variant_t = std::variant<Vnil, Vcons>;

  private:
    // DATA
    variant_t d_v_;

    // CREATORS
    explicit vec(Vnil _v) : d_v_(std::move(_v)) {}

    explicit vec(Vcons _v) : d_v_(std::move(_v)) {}

  public:
    // TYPES
    struct ctor {
      ctor() = delete;

      static std::shared_ptr<vec<t_A>> Vnil_() {
        return std::shared_ptr<vec<t_A>>(new vec<t_A>(Vnil{}));
      }

      static std::shared_ptr<vec<t_A>>
      Vcons_(unsigned int a0, t_A a1, const std::shared_ptr<vec<t_A>> &a2) {
        return std::shared_ptr<vec<t_A>>(new vec<t_A>(Vcons{a0, a1, a2}));
      }

      static std::unique_ptr<vec<t_A>> Vnil_uptr() {
        return std::unique_ptr<vec<t_A>>(new vec<t_A>(Vnil{}));
      }

      static std::unique_ptr<vec<t_A>>
      Vcons_uptr(unsigned int a0, t_A a1, const std::shared_ptr<vec<t_A>> &a2) {
        return std::unique_ptr<vec<t_A>>(new vec<t_A>(Vcons{a0, a1, a2}));
      }
    };

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, typename T2,
            MapsTo<T2, unsigned int, T1, std::shared_ptr<vec<T1>>, T2> F1>
  static T2 vec_rect(const T2 f, F1 &&f0, const unsigned int _x,
                     const std::shared_ptr<vec<T1>> &v) {
    return std::visit(
        Overloaded{[&](const typename vec<T1>::Vnil _args) -> T2 { return f; },
                   [&](const typename vec<T1>::Vcons _args) -> T2 {
                     unsigned int n = _args.d_a0;
                     T1 y = _args.d_a1;
                     std::shared_ptr<vec<T1>> v0 = _args.d_a2;
                     return f0(n, y, v0, vec_rect<T1, T2>(f, f0, n, v0));
                   }},
        v->v());
  }

  template <typename T1, typename T2,
            MapsTo<T2, unsigned int, T1, std::shared_ptr<vec<T1>>, T2> F1>
  static T2 vec_rec(const T2 f, F1 &&f0, const unsigned int _x,
                    const std::shared_ptr<vec<T1>> &v) {
    return std::visit(
        Overloaded{[&](const typename vec<T1>::Vnil _args) -> T2 { return f; },
                   [&](const typename vec<T1>::Vcons _args) -> T2 {
                     unsigned int n = _args.d_a0;
                     T1 y = _args.d_a1;
                     std::shared_ptr<vec<T1>> v0 = _args.d_a2;
                     return f0(n, y, v0, vec_rec<T1, T2>(f, f0, n, v0));
                   }},
        v->v());
  }

  template <typename T1>
  static std::shared_ptr<List<T1>>
  vec_to_list(const unsigned int _x, const std::shared_ptr<vec<T1>> &v) {
    return std::visit(
        Overloaded{
            [](const typename vec<T1>::Vnil _args)
                -> std::shared_ptr<List<T1>> { return List<T1>::ctor::Nil_(); },
            [](const typename vec<T1>::Vcons _args)
                -> std::shared_ptr<List<T1>> {
              unsigned int n0 = _args.d_a0;
              T1 x = _args.d_a1;
              std::shared_ptr<vec<T1>> xs = _args.d_a2;
              return List<T1>::ctor::Cons_(
                  x, vec_to_list<T1>(std::move(n0), std::move(xs)));
            }},
        v->v());
  }

  template <typename T1, typename T2, MapsTo<T2, T1> F1>
  static std::shared_ptr<vec<T2>> vec_map(const unsigned int _x, F1 &&f,
                                          const std::shared_ptr<vec<T1>> &v) {
    return std::visit(
        Overloaded{
            [](const typename vec<T1>::Vnil _args) -> std::shared_ptr<vec<T2>> {
              return vec<T2>::ctor::Vnil_();
            },
            [&](const typename vec<T1>::Vcons _args)
                -> std::shared_ptr<vec<T2>> {
              unsigned int n0 = _args.d_a0;
              T1 x = _args.d_a1;
              std::shared_ptr<vec<T1>> xs = _args.d_a2;
              return vec<T2>::ctor::Vcons_(
                  n0, f(x), vec_map<T1, T2>(n0, f, std::move(xs)));
            }},
        v->v());
  }

  template <typename T1>
  static T1 vec_head(const unsigned int _x, const std::shared_ptr<vec<T1>> &v) {
    return std::visit(Overloaded{[](const typename vec<T1>::Vnil _args) -> T1 {
                                   throw std::logic_error("unreachable");
                                 },
                                 [](const typename vec<T1>::Vcons _args) -> T1 {
                                   T1 x = _args.d_a1;
                                   return x;
                                 }},
                      v->v());
  }

  template <typename T1>
  static std::shared_ptr<vec<T1>> vec_tail(const unsigned int _x,
                                           const std::shared_ptr<vec<T1>> &v) {
    return std::visit(
        Overloaded{
            [](const typename vec<T1>::Vnil _args) -> std::shared_ptr<vec<T1>> {
              throw std::logic_error("unreachable");
            },
            [](const typename vec<T1>::Vcons _args)
                -> std::shared_ptr<vec<T1>> {
              std::shared_ptr<vec<T1>> xs = _args.d_a2;
              return std::move(xs);
            }},
        v->v());
  }

  struct avail {
    // TYPES
    struct Present {
      unsigned int d_a0;
    };

    struct Absent {};

    using variant_t = std::variant<Present, Absent>;

  private:
    // DATA
    variant_t d_v_;

    // CREATORS
    explicit avail(Present _v) : d_v_(std::move(_v)) {}

    explicit avail(Absent _v) : d_v_(std::move(_v)) {}

  public:
    // TYPES
    struct ctor {
      ctor() = delete;

      static std::shared_ptr<avail> Present_(unsigned int a0) {
        return std::shared_ptr<avail>(new avail(Present{a0}));
      }

      static std::shared_ptr<avail> Absent_() {
        return std::shared_ptr<avail>(new avail(Absent{}));
      }

      static std::unique_ptr<avail> Present_uptr(unsigned int a0) {
        return std::unique_ptr<avail>(new avail(Present{a0}));
      }

      static std::unique_ptr<avail> Absent_uptr() {
        return std::unique_ptr<avail>(new avail(Absent{}));
      }
    };

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, unsigned int> F0>
  static T1 avail_rect(F0 &&f, const T1 f0, const bool _x,
                       const std::shared_ptr<avail> &a) {
    return std::visit(
        Overloaded{
            [&](const typename avail::Present _args) -> T1 {
              unsigned int n = _args.d_a0;
              return f(std::move(n));
            },
            [&](const typename avail::Absent _args) -> T1 { return f0; }},
        a->v());
  }

  template <typename T1, MapsTo<T1, unsigned int> F0>
  static T1 avail_rec(F0 &&f, const T1 f0, const bool _x,
                      const std::shared_ptr<avail> &a) {
    return std::visit(
        Overloaded{
            [&](const typename avail::Present _args) -> T1 {
              unsigned int n = _args.d_a0;
              return f(std::move(n));
            },
            [&](const typename avail::Absent _args) -> T1 { return f0; }},
        a->v());
  }

  __attribute__((pure)) static unsigned int
  get_present(const std::shared_ptr<avail> &a);
  static inline const unsigned int test_fin0 =
      fin_to_nat(3u, fin::ctor::FZ_(2u));
  static inline const unsigned int test_fin2 = fin_to_nat(
      3u, fin::ctor::FS_(2u, fin::ctor::FS_(1u, fin::ctor::FZ_(0u))));
  static inline const std::shared_ptr<vec<unsigned int>> my_vec =
      vec<unsigned int>::ctor::Vcons_(
          2u, 10u,
          vec<unsigned int>::ctor::Vcons_(
              1u, 20u,
              vec<unsigned int>::ctor::Vcons_(
                  0u, 30u, vec<unsigned int>::ctor::Vnil_())));
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
      get_present(avail::ctor::Present_(42u));
};

#endif // INCLUDED_DEP_ELIM
