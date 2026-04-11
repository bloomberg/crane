#ifndef INCLUDED_UNIT_TYPE
#define INCLUDED_UNIT_TYPE

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

struct UnitType {
  static inline const std::monostate unit_val = std::monostate{};
  static void return_unit(const unsigned int _x);
  __attribute__((pure)) static unsigned int take_unit(const std::monostate _x);
  __attribute__((pure)) static unsigned int match_unit(const std::monostate u);

  template <typename t_A, typename t_B> struct pair {
    // TYPES
    struct Pair0 {
      t_A d_a0;
      t_B d_a1;
    };

    using variant_t = std::variant<Pair0>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    explicit pair(Pair0 _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<pair<t_A, t_B>> pair0(t_A a0, t_B a1) {
      return std::make_shared<pair<t_A, t_B>>(
          Pair0{std::move(a0), std::move(a1)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, typename T2, typename T3, MapsTo<T3, T1, T2> F0>
  static T3 pair_rect(F0 &&f, const std::shared_ptr<pair<T1, T2>> &p) {
    return std::visit(
        Overloaded{[&](const typename pair<T1, T2>::Pair0 _args) -> T3 {
          return f(_args.d_a0, _args.d_a1);
        }},
        p->v());
  }

  template <typename T1, typename T2, typename T3, MapsTo<T3, T1, T2> F0>
  static T3 pair_rec(F0 &&f, const std::shared_ptr<pair<T1, T2>> &p) {
    return std::visit(
        Overloaded{[&](const typename pair<T1, T2>::Pair0 _args) -> T3 {
          return f(_args.d_a0, _args.d_a1);
        }},
        p->v());
  }

  static inline const std::shared_ptr<pair<unsigned int, std::monostate>>
      pair_with_unit =
          pair<unsigned int, std::monostate>::pair0(3u, std::monostate{});
  static inline const std::shared_ptr<pair<std::monostate, std::monostate>>
      unit_pair = pair<std::monostate, std::monostate>::pair0(std::monostate{},
                                                              std::monostate{});
  static void unit_to_unit(const std::monostate u);

  template <typename T1, typename T2> static T2 seq(const T1, const T2 b) {
    return b;
  }

  static inline const unsigned int sequenced =
      seq<std::monostate, unsigned int>(
          std::monostate{},
          seq<std::monostate, unsigned int>(std::monostate{}, 5u));
  static inline const unsigned int test_take = take_unit(std::monostate{});
  static inline const unsigned int test_match = match_unit(std::monostate{});
  static inline const unsigned int test_seq = sequenced;
};

#endif // INCLUDED_UNIT_TYPE
