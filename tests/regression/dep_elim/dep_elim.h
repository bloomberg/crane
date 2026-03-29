#ifndef INCLUDED_DEP_ELIM
#define INCLUDED_DEP_ELIM

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

public:
  // CREATORS
  explicit List(Nil _v) : d_v_(std::move(_v)) {}

  explicit List(Cons _v) : d_v_(std::move(_v)) {}

  static std::shared_ptr<List<t_A>> nil() {
    return std::make_shared<List<t_A>>(Nil{});
  }

  static std::shared_ptr<List<t_A>> cons(t_A a0,
                                         const std::shared_ptr<List<t_A>> &a1) {
    return std::make_shared<List<t_A>>(Cons{std::move(a0), a1});
  }

  static std::shared_ptr<List<t_A>> cons(t_A a0,
                                         std::shared_ptr<List<t_A>> &&a1) {
    return std::make_shared<List<t_A>>(Cons{std::move(a0), std::move(a1)});
  }

  static std::unique_ptr<List<t_A>> nil_uptr() {
    return std::make_unique<List<t_A>>(Nil{});
  }

  static std::unique_ptr<List<t_A>>
  cons_uptr(t_A a0, const std::shared_ptr<List<t_A>> &a1) {
    return std::make_unique<List<t_A>>(Cons{std::move(a0), a1});
  }

  static std::unique_ptr<List<t_A>> cons_uptr(t_A a0,
                                              std::shared_ptr<List<t_A>> &&a1) {
    return std::make_unique<List<t_A>>(Cons{std::move(a0), std::move(a1)});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
};

struct DepElim {
  struct fin {
    // TYPES
    struct FZ {
      unsigned int d_n;
    };

    struct FS {
      unsigned int d_n;
      std::shared_ptr<fin> d_a1;
    };

    using variant_t = std::variant<FZ, FS>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    explicit fin(FZ _v) : d_v_(std::move(_v)) {}

    explicit fin(FS _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<fin> fz(unsigned int n) {
      return std::make_shared<fin>(FZ{std::move(n)});
    }

    static std::shared_ptr<fin> fs(unsigned int n,
                                   const std::shared_ptr<fin> &a1) {
      return std::make_shared<fin>(FS{std::move(n), a1});
    }

    static std::shared_ptr<fin> fs(unsigned int n, std::shared_ptr<fin> &&a1) {
      return std::make_shared<fin>(FS{std::move(n), std::move(a1)});
    }

    static std::unique_ptr<fin> fz_uptr(unsigned int n) {
      return std::make_unique<fin>(FZ{std::move(n)});
    }

    static std::unique_ptr<fin> fs_uptr(unsigned int n,
                                        const std::shared_ptr<fin> &a1) {
      return std::make_unique<fin>(FS{std::move(n), a1});
    }

    static std::unique_ptr<fin> fs_uptr(unsigned int n,
                                        std::shared_ptr<fin> &&a1) {
      return std::make_unique<fin>(FS{std::move(n), std::move(a1)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    __attribute__((pure)) unsigned int fin_to_nat(const unsigned int _x) const {
      return std::visit(
          Overloaded{
              [](const typename fin::FZ _args) -> unsigned int { return 0u; },
              [](const typename fin::FS _args) -> unsigned int {
                return (_args.d_a1->fin_to_nat(_args.d_n) + 1);
              }},
          this->v());
    }

    template <typename T1, MapsTo<T1, unsigned int> F0,
              MapsTo<T1, unsigned int, std::shared_ptr<fin>, T1> F1>
    T1 fin_rec(F0 &&f, F1 &&f0, const unsigned int _x) const {
      return std::visit(
          Overloaded{
              [&](const typename fin::FZ _args) -> T1 { return f(_args.d_n); },
              [&](const typename fin::FS _args) -> T1 {
                return f0(_args.d_n, _args.d_a1,
                          _args.d_a1->template fin_rec<T1>(f, f0, _args.d_n));
              }},
          this->v());
    }

    template <typename T1, MapsTo<T1, unsigned int> F0,
              MapsTo<T1, unsigned int, std::shared_ptr<fin>, T1> F1>
    T1 fin_rect(F0 &&f, F1 &&f0, const unsigned int _x) const {
      return std::visit(
          Overloaded{
              [&](const typename fin::FZ _args) -> T1 { return f(_args.d_n); },
              [&](const typename fin::FS _args) -> T1 {
                return f0(_args.d_n, _args.d_a1,
                          _args.d_a1->template fin_rect<T1>(f, f0, _args.d_n));
              }},
          this->v());
    }
  };

  template <typename t_A> struct vec {
    // TYPES
    struct Vnil {};

    struct Vcons {
      unsigned int d_n;
      t_A d_a1;
      std::shared_ptr<vec<t_A>> d_a2;
    };

    using variant_t = std::variant<Vnil, Vcons>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    explicit vec(Vnil _v) : d_v_(std::move(_v)) {}

    explicit vec(Vcons _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<vec<t_A>> vnil() {
      return std::make_shared<vec<t_A>>(Vnil{});
    }

    static std::shared_ptr<vec<t_A>>
    vcons(unsigned int n, t_A a1, const std::shared_ptr<vec<t_A>> &a2) {
      return std::make_shared<vec<t_A>>(Vcons{std::move(n), std::move(a1), a2});
    }

    static std::shared_ptr<vec<t_A>> vcons(unsigned int n, t_A a1,
                                           std::shared_ptr<vec<t_A>> &&a2) {
      return std::make_shared<vec<t_A>>(
          Vcons{std::move(n), std::move(a1), std::move(a2)});
    }

    static std::unique_ptr<vec<t_A>> vnil_uptr() {
      return std::make_unique<vec<t_A>>(Vnil{});
    }

    static std::unique_ptr<vec<t_A>>
    vcons_uptr(unsigned int n, t_A a1, const std::shared_ptr<vec<t_A>> &a2) {
      return std::make_unique<vec<t_A>>(Vcons{std::move(n), std::move(a1), a2});
    }

    static std::unique_ptr<vec<t_A>>
    vcons_uptr(unsigned int n, t_A a1, std::shared_ptr<vec<t_A>> &&a2) {
      return std::make_unique<vec<t_A>>(
          Vcons{std::move(n), std::move(a1), std::move(a2)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    std::shared_ptr<vec<t_A>> vec_tail(const unsigned int _x) const {
      return std::visit(
          Overloaded{[](const typename vec<t_A>::Vnil _args)
                         -> std::shared_ptr<vec<t_A>> {
                       throw std::logic_error("unreachable");
                     },
                     [](const typename vec<t_A>::Vcons _args)
                         -> std::shared_ptr<vec<t_A>> { return _args.d_a2; }},
          this->v());
    }

    t_A vec_head(const unsigned int _x) const {
      return std::visit(
          Overloaded{[](const typename vec<t_A>::Vnil _args) -> t_A {
                       throw std::logic_error("unreachable");
                     },
                     [](const typename vec<t_A>::Vcons _args) -> t_A {
                       return _args.d_a1;
                     }},
          this->v());
    }

    template <typename T1, MapsTo<T1, t_A> F1>
    std::shared_ptr<vec<T1>> vec_map(const unsigned int _x, F1 &&f) const {
      return std::visit(
          Overloaded{
              [](const typename vec<t_A>::Vnil _args)
                  -> std::shared_ptr<vec<T1>> { return vec<T1>::vnil(); },
              [&](const typename vec<t_A>::Vcons _args)
                  -> std::shared_ptr<vec<T1>> {
                return vec<T1>::vcons(
                    _args.d_n, f(_args.d_a1),
                    _args.d_a2->template vec_map<T1>(_args.d_n, f));
              }},
          this->v());
    }

    std::shared_ptr<List<t_A>> vec_to_list(const unsigned int _x) const {
      return std::visit(
          Overloaded{
              [](const typename vec<t_A>::Vnil _args)
                  -> std::shared_ptr<List<t_A>> { return List<t_A>::nil(); },
              [](const typename vec<t_A>::Vcons _args)
                  -> std::shared_ptr<List<t_A>> {
                return List<t_A>::cons(_args.d_a1,
                                       _args.d_a2->vec_to_list(_args.d_n));
              }},
          this->v());
    }
  };

  template <typename T1, typename T2,
            MapsTo<T2, unsigned int, T1, std::shared_ptr<vec<T1>>, T2> F1>
  static T2 vec_rect(const T2 f, F1 &&f0, const unsigned int _x,
                     const std::shared_ptr<vec<T1>> &v) {
    return std::visit(
        Overloaded{[&](const typename vec<T1>::Vnil _args) -> T2 { return f; },
                   [&](const typename vec<T1>::Vcons _args) -> T2 {
                     return f0(_args.d_n, _args.d_a1, _args.d_a2,
                               vec_rect<T1, T2>(f, f0, _args.d_n, _args.d_a2));
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
                     return f0(_args.d_n, _args.d_a1, _args.d_a2,
                               vec_rec<T1, T2>(f, f0, _args.d_n, _args.d_a2));
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

  public:
    // CREATORS
    explicit avail(Present _v) : d_v_(std::move(_v)) {}

    explicit avail(Absent _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<avail> present(unsigned int a0) {
      return std::make_shared<avail>(Present{std::move(a0)});
    }

    static std::shared_ptr<avail> absent() {
      return std::make_shared<avail>(Absent{});
    }

    static std::unique_ptr<avail> present_uptr(unsigned int a0) {
      return std::make_unique<avail>(Present{std::move(a0)});
    }

    static std::unique_ptr<avail> absent_uptr() {
      return std::make_unique<avail>(Absent{});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    __attribute__((pure)) unsigned int get_present() const {
      return std::visit(
          Overloaded{[](const typename avail::Present _args) -> unsigned int {
                       return _args.d_a0;
                     },
                     [](const typename avail::Absent _args) -> unsigned int {
                       throw std::logic_error("unreachable");
                     }},
          this->v());
    }

    template <typename T1, MapsTo<T1, unsigned int> F0>
    T1 avail_rec(F0 &&f, const T1 f0, const bool _x) const {
      return std::visit(
          Overloaded{
              [&](const typename avail::Present _args) -> T1 {
                return f(_args.d_a0);
              },
              [&](const typename avail::Absent _args) -> T1 { return f0; }},
          this->v());
    }

    template <typename T1, MapsTo<T1, unsigned int> F0>
    T1 avail_rect(F0 &&f, const T1 f0, const bool _x) const {
      return std::visit(
          Overloaded{
              [&](const typename avail::Present _args) -> T1 {
                return f(_args.d_a0);
              },
              [&](const typename avail::Absent _args) -> T1 { return f0; }},
          this->v());
    }
  };

  static inline const unsigned int test_fin0 = fin::fz(2u)->fin_to_nat(3u);
  static inline const unsigned int test_fin2 =
      fin::fs(2u, fin::fs(1u, fin::fz(0u)))->fin_to_nat(3u);
  static inline const std::shared_ptr<vec<unsigned int>> my_vec =
      vec<unsigned int>::vcons(
          2u, 10u,
          vec<unsigned int>::vcons(
              1u, 20u,
              vec<unsigned int>::vcons(0u, 30u, vec<unsigned int>::vnil())));
  static inline const std::shared_ptr<List<unsigned int>> test_vec_list =
      my_vec->vec_to_list(3u);
  static inline const unsigned int test_vec_head = my_vec->vec_head(2u);
  static inline const std::shared_ptr<List<unsigned int>> test_vec_tail_list =
      my_vec->vec_tail(2u)->vec_to_list(2u);
  static inline const std::shared_ptr<List<unsigned int>> test_vec_map =
      my_vec
          ->template vec_map<unsigned int>(
              3u, [](unsigned int n) { return (n + 1u); })
          ->vec_to_list(3u);
  static inline const unsigned int test_present =
      avail::present(42u)->get_present();
};

#endif // INCLUDED_DEP_ELIM
