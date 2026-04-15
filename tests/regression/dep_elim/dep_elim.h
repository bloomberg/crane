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
  explicit List(Nil _v) : d_v_(_v) {}

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

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    __attribute__((pure)) unsigned int fin_to_nat(const unsigned int) const {
      if (std::holds_alternative<typename fin::FZ>(this->v())) {
        return 0u;
      } else {
        const auto &[d_n, d_a1] = std::get<typename fin::FS>(this->v());
        return (d_a1->fin_to_nat(d_n) + 1);
      }
    }

    template <typename T1, MapsTo<T1, unsigned int> F0,
              MapsTo<T1, unsigned int, std::shared_ptr<fin>, T1> F1>
    T1 fin_rec(F0 &&f, F1 &&f0, const unsigned int) const {
      if (std::holds_alternative<typename fin::FZ>(this->v())) {
        const auto &[d_n] = std::get<typename fin::FZ>(this->v());
        return f(d_n);
      } else {
        const auto &[d_n, d_a1] = std::get<typename fin::FS>(this->v());
        return f0(d_n, d_a1, d_a1->template fin_rec<T1>(f, f0, d_n));
      }
    }

    template <typename T1, MapsTo<T1, unsigned int> F0,
              MapsTo<T1, unsigned int, std::shared_ptr<fin>, T1> F1>
    T1 fin_rect(F0 &&f, F1 &&f0, const unsigned int) const {
      if (std::holds_alternative<typename fin::FZ>(this->v())) {
        const auto &[d_n] = std::get<typename fin::FZ>(this->v());
        return f(d_n);
      } else {
        const auto &[d_n, d_a1] = std::get<typename fin::FS>(this->v());
        return f0(d_n, d_a1, d_a1->template fin_rect<T1>(f, f0, d_n));
      }
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
    explicit vec(Vnil _v) : d_v_(_v) {}

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

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    std::shared_ptr<vec<t_A>> vec_tail(const unsigned int) const {
      if (std::holds_alternative<typename vec<t_A>::Vnil>(this->v())) {
        throw std::logic_error("unreachable");
      } else {
        const auto &[d_n, d_a1, d_a2] =
            std::get<typename vec<t_A>::Vcons>(this->v());
        return d_a2;
      }
    }

    t_A vec_head(const unsigned int) const {
      if (std::holds_alternative<typename vec<t_A>::Vnil>(this->v())) {
        throw std::logic_error("unreachable");
      } else {
        const auto &[d_n, d_a1, d_a2] =
            std::get<typename vec<t_A>::Vcons>(this->v());
        return d_a1;
      }
    }

    template <typename T1, MapsTo<T1, t_A> F1>
    std::shared_ptr<vec<T1>> vec_map(const unsigned int, F1 &&f) const {
      if (std::holds_alternative<typename vec<t_A>::Vnil>(this->v())) {
        return vec<T1>::vnil();
      } else {
        const auto &[d_n, d_a1, d_a2] =
            std::get<typename vec<t_A>::Vcons>(this->v());
        return vec<T1>::vcons(d_n, f(d_a1), d_a2->template vec_map<T1>(d_n, f));
      }
    }

    std::shared_ptr<List<t_A>> vec_to_list(const unsigned int) const {
      if (std::holds_alternative<typename vec<t_A>::Vnil>(this->v())) {
        return List<t_A>::nil();
      } else {
        const auto &[d_n, d_a1, d_a2] =
            std::get<typename vec<t_A>::Vcons>(this->v());
        return List<t_A>::cons(d_a1, d_a2->vec_to_list(d_n));
      }
    }

    template <typename T1,
              MapsTo<T1, unsigned int, t_A, std::shared_ptr<vec<t_A>>, T1> F1>
    T1 vec_rec(const T1 f, F1 &&f0, const unsigned int) const {
      if (std::holds_alternative<typename vec<t_A>::Vnil>(this->v())) {
        return f;
      } else {
        const auto &[d_n, d_a1, d_a2] =
            std::get<typename vec<t_A>::Vcons>(this->v());
        return f0(d_n, d_a1, d_a2, d_a2->template vec_rec<T1>(f, f0, d_n));
      }
    }

    template <typename T1,
              MapsTo<T1, unsigned int, t_A, std::shared_ptr<vec<t_A>>, T1> F1>
    T1 vec_rect(const T1 f, F1 &&f0, const unsigned int) const {
      if (std::holds_alternative<typename vec<t_A>::Vnil>(this->v())) {
        return f;
      } else {
        const auto &[d_n, d_a1, d_a2] =
            std::get<typename vec<t_A>::Vcons>(this->v());
        return f0(d_n, d_a1, d_a2, d_a2->template vec_rect<T1>(f, f0, d_n));
      }
    }
  };

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

    explicit avail(Absent _v) : d_v_(_v) {}

    static std::shared_ptr<avail> present(unsigned int a0) {
      return std::make_shared<avail>(Present{std::move(a0)});
    }

    static std::shared_ptr<avail> absent() {
      return std::make_shared<avail>(Absent{});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    __attribute__((pure)) unsigned int get_present() const {
      if (std::holds_alternative<typename avail::Present>(this->v())) {
        const auto &[d_a0] = std::get<typename avail::Present>(this->v());
        return d_a0;
      } else {
        throw std::logic_error("unreachable");
      }
    }

    template <typename T1, MapsTo<T1, unsigned int> F0>
    T1 avail_rec(F0 &&f, const T1 f0, const bool) const {
      if (std::holds_alternative<typename avail::Present>(this->v())) {
        const auto &[d_a0] = std::get<typename avail::Present>(this->v());
        return f(d_a0);
      } else {
        return f0;
      }
    }

    template <typename T1, MapsTo<T1, unsigned int> F0>
    T1 avail_rect(F0 &&f, const T1 f0, const bool) const {
      if (std::holds_alternative<typename avail::Present>(this->v())) {
        const auto &[d_a0] = std::get<typename avail::Present>(this->v());
        return f(d_a0);
      } else {
        return f0;
      }
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
              3u, [](const unsigned int n) { return (n + 1u); })
          ->vec_to_list(3u);
  static inline const unsigned int test_present =
      avail::present(42u)->get_present();
};

#endif // INCLUDED_DEP_ELIM
