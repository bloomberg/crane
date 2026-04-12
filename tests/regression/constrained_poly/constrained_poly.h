#ifndef INCLUDED_CONSTRAINED_POLY
#define INCLUDED_CONSTRAINED_POLY

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

struct ConstrainedPoly {
  template <typename T1> static T1 poly_id(const T1 x) { return x; }

  template <typename t_A, typename t_B> struct UPair {
    t_A ufst;
    t_B usnd;
  };

  template <typename T1, typename T2>
  static std::shared_ptr<UPair<T2, T1>>
  swap(const std::shared_ptr<UPair<T1, T2>> &p) {
    return std::make_shared<UPair<T2, T1>>(UPair<T2, T1>{p->usnd, p->ufst});
  }

  template <typename T1, typename T2>
  static std::shared_ptr<UPair<T1, T2>> wrap_pair(const T1 a, const T2 b) {
    return std::make_shared<UPair<T1, T2>>(UPair<T1, T2>{a, b});
  }

  template <typename t_A> struct UOption {
    // TYPES
    struct USome {
      t_A d_a0;
    };

    struct UNone {};

    using variant_t = std::variant<USome, UNone>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    explicit UOption(USome _v) : d_v_(std::move(_v)) {}

    explicit UOption(UNone _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<UOption<t_A>> usome(t_A a0) {
      return std::make_shared<UOption<t_A>>(USome{std::move(a0)});
    }

    static std::shared_ptr<UOption<t_A>> unone() {
      return std::make_shared<UOption<t_A>>(UNone{});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, typename T2, MapsTo<T2, T1> F0>
  static T2 UOption_rect(F0 &&f, const T2 f0,
                         const std::shared_ptr<UOption<T1>> &u) {
    return std::visit(
        Overloaded{[&](const typename UOption<T1>::USome _args) -> T2 {
                     return f(_args.d_a0);
                   },
                   [&](const typename UOption<T1>::UNone) -> T2 { return f0; }},
        u->v());
  }

  template <typename T1, typename T2, MapsTo<T2, T1> F0>
  static T2 UOption_rec(F0 &&f, const T2 f0,
                        const std::shared_ptr<UOption<T1>> &u) {
    return std::visit(
        Overloaded{[&](const typename UOption<T1>::USome _args) -> T2 {
                     return f(_args.d_a0);
                   },
                   [&](const typename UOption<T1>::UNone) -> T2 { return f0; }},
        u->v());
  }

  template <typename T1, typename T2, MapsTo<T2, T1> F0>
  static std::shared_ptr<UOption<T2>>
  uoption_map(F0 &&f, const std::shared_ptr<UOption<T1>> &o) {
    return std::visit(Overloaded{[&](const typename UOption<T1>::USome _args)
                                     -> std::shared_ptr<UOption<T2>> {
                                   return UOption<T2>::usome(f(_args.d_a0));
                                 },
                                 [](const typename UOption<T1>::UNone)
                                     -> std::shared_ptr<UOption<T2>> {
                                   return UOption<T2>::unone();
                                 }},
                      o->v());
  }

  static inline const unsigned int test_id_nat = poly_id<unsigned int>(42u);
  static inline const bool test_id_bool = poly_id<bool>(true);
  static inline const std::shared_ptr<UPair<unsigned int, bool>> test_pair =
      wrap_pair<unsigned int, bool>(5u, false);
  static inline const std::shared_ptr<UPair<bool, unsigned int>> test_swap =
      swap<unsigned int, bool>(test_pair);
  static inline const unsigned int test_fst = test_pair->ufst;
  static inline const bool test_snd = test_pair->usnd;
  static inline const std::shared_ptr<UOption<unsigned int>> test_umap =
      uoption_map<unsigned int, unsigned int>(
          [](unsigned int n) { return (n + 1u); },
          UOption<unsigned int>::usome(9u));
};

#endif // INCLUDED_CONSTRAINED_POLY
