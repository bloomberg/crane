#ifndef INCLUDED_UNIVERSE_POLY
#define INCLUDED_UNIVERSE_POLY

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

template <typename t_A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    t_A d_a0;
    std::unique_ptr<List<t_A>> d_a1;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  List() {}

  explicit List(Nil _v) : d_v_(_v) {}

  explicit List(Cons _v) : d_v_(std::move(_v)) {}

  List(const List<t_A> &_other) : d_v_(std::move(_other.clone().d_v_)) {}

  List(List<t_A> &&_other) : d_v_(std::move(_other.d_v_)) {}

  List<t_A> &operator=(const List<t_A> &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  List<t_A> &operator=(List<t_A> &&_other) {
    d_v_ = std::move(_other.d_v_);
    return *this;
  }

  // ACCESSORS
  __attribute__((pure)) List<t_A> clone() const {
    auto &&_sv = *(this);
    if (std::holds_alternative<Nil>(_sv.v())) {
      return List<t_A>(Nil{});
    } else {
      const auto &[d_a0, d_a1] = std::get<Cons>(_sv.v());
      return List<t_A>(Cons{
          d_a0, d_a1 ? std::make_unique<List<t_A>>(d_a1->clone()) : nullptr});
    }
  }

  // CREATORS
  template <typename _U> explicit List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      d_v_ = Nil{};
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<_U>::Cons>(_other.v());
      d_v_ =
          Cons{t_A(d_a0), d_a1 ? std::make_unique<List<t_A>>(*d_a1) : nullptr};
    }
  }

  __attribute__((pure)) static List<t_A> nil() { return List(Nil{}); }

  __attribute__((pure)) static List<t_A> cons(t_A a0, List<t_A> a1) {
    return List(
        Cons{std::move(a0), std::make_unique<List<t_A>>(std::move(a1))});
  }

  // MANIPULATORS
  inline variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
};

struct UniversePoly {
  template <typename T1> static T1 poly_id(const T1 x) { return x; }

  static inline const unsigned int test_id_nat = poly_id<unsigned int>(42u);
  static inline const bool test_id_bool = poly_id<bool>(true);

  template <typename t_A, typename t_B> struct ppair {
    t_A pfst;
    t_B psnd;

    // ACCESSORS
    __attribute__((pure)) ppair<t_A, t_B> clone() const {
      return ppair<t_A, t_B>{(*(this)).pfst, (*(this)).psnd};
    }
  };

  static inline const ppair<unsigned int, bool> test_pair =
      ppair<unsigned int, bool>{5u, true};
  static inline const unsigned int test_pfst = test_pair.pfst;
  static inline const bool test_psnd = test_pair.psnd;

  template <typename t_A> struct poption {
    // TYPES
    struct Pnone {};

    struct Psome {
      t_A d_a0;
    };

    using variant_t = std::variant<Pnone, Psome>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    poption() {}

    explicit poption(Pnone _v) : d_v_(_v) {}

    explicit poption(Psome _v) : d_v_(std::move(_v)) {}

    poption(const poption<t_A> &_other)
        : d_v_(std::move(_other.clone().d_v_)) {}

    poption(poption<t_A> &&_other) : d_v_(std::move(_other.d_v_)) {}

    poption<t_A> &operator=(const poption<t_A> &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    poption<t_A> &operator=(poption<t_A> &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) poption<t_A> clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<Pnone>(_sv.v())) {
        return poption<t_A>(Pnone{});
      } else {
        const auto &[d_a0] = std::get<Psome>(_sv.v());
        return poption<t_A>(Psome{d_a0});
      }
    }

    // CREATORS
    template <typename _U> explicit poption(const poption<_U> &_other) {
      if (std::holds_alternative<typename poption<_U>::Pnone>(_other.v())) {
        d_v_ = Pnone{};
      } else {
        const auto &[d_a0] = std::get<typename poption<_U>::Psome>(_other.v());
        d_v_ = Psome{t_A(d_a0)};
      }
    }

    __attribute__((pure)) static poption<t_A> pnone() {
      return poption(Pnone{});
    }

    __attribute__((pure)) static poption<t_A> psome(t_A a0) {
      return poption(Psome{std::move(a0)});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, typename T2, MapsTo<T2, T1> F1>
  static T2 poption_rect(const T2 f, F1 &&f0, const poption<T1> &p) {
    if (std::holds_alternative<typename poption<T1>::Pnone>(p.v())) {
      return f;
    } else {
      const auto &[d_a0] = std::get<typename poption<T1>::Psome>(p.v());
      return f0(d_a0);
    }
  }

  template <typename T1, typename T2, MapsTo<T2, T1> F1>
  static T2 poption_rec(const T2 f, F1 &&f0, const poption<T1> &p) {
    if (std::holds_alternative<typename poption<T1>::Pnone>(p.v())) {
      return f;
    } else {
      const auto &[d_a0] = std::get<typename poption<T1>::Psome>(p.v());
      return f0(d_a0);
    }
  }

  template <typename T1, typename T2, MapsTo<T2, T1> F0>
  __attribute__((pure)) static poption<T2> poption_map(F0 &&f,
                                                       const poption<T1> &o) {
    if (std::holds_alternative<typename poption<T1>::Pnone>(o.v())) {
      return poption<T2>::pnone();
    } else {
      const auto &[d_a0] = std::get<typename poption<T1>::Psome>(o.v());
      return poption<T2>::psome(f(d_a0));
    }
  }

  template <typename T1, typename T2, MapsTo<poption<T2>, T1> F1>
  __attribute__((pure)) static poption<T2> poption_bind(const poption<T1> &o,
                                                        F1 &&f) {
    if (std::holds_alternative<typename poption<T1>::Pnone>(o.v())) {
      return poption<T2>::pnone();
    } else {
      const auto &[d_a0] = std::get<typename poption<T1>::Psome>(o.v());
      return f(d_a0);
    }
  }

  static inline const poption<unsigned int> test_map_some =
      poption_map<unsigned int, unsigned int>(
          [](const unsigned int &n) { return (n + 1u); },
          poption<unsigned int>::psome(5u));
  static inline const poption<unsigned int> test_map_none =
      poption_map<unsigned int, unsigned int>(
          [](const unsigned int &n) { return (n + 1u); },
          poption<unsigned int>::pnone());
  static inline const poption<unsigned int> test_bind =
      poption_bind<unsigned int, unsigned int>(
          poption<unsigned int>::psome(3u), [](const unsigned int &n) {
            return poption<unsigned int>::psome((n + n));
          });

  template <typename T1>
  __attribute__((pure)) static unsigned int poly_length(const List<T1> &l) {
    if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
      return 0u;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<T1>::Cons>(l.v());
      return (poly_length<T1>(*(d_a1)) + 1);
    }
  }

  static inline const unsigned int test_length =
      poly_length<unsigned int>(List<unsigned int>::cons(
          1u,
          List<unsigned int>::cons(
              2u, List<unsigned int>::cons(3u, List<unsigned int>::nil()))));
};

#endif // INCLUDED_UNIVERSE_POLY
