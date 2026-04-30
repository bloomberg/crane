#ifndef INCLUDED_UNIT_TYPE
#define INCLUDED_UNIT_TYPE

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

struct UnitType {
  static inline const std::monostate unit_val = std::monostate{};
  static void return_unit(const unsigned int &_x);
  static unsigned int take_unit(const std::monostate &_x);
  static unsigned int match_unit(const std::monostate &u);

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
    pair() {}

    explicit pair(Pair0 _v) : d_v_(std::move(_v)) {}

    pair(const pair<t_A, t_B> &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    pair(pair<t_A, t_B> &&_other) : d_v_(std::move(_other.d_v_)) {}

    pair<t_A, t_B> &operator=(const pair<t_A, t_B> &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    pair<t_A, t_B> &operator=(pair<t_A, t_B> &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    pair<t_A, t_B> clone() const {
      auto &&_sv = *(this);
      const auto &[d_a0, d_a1] = std::get<Pair0>(_sv.v());
      return pair<t_A, t_B>(Pair0{d_a0, d_a1});
    }

    // CREATORS
    template <typename _U0, typename _U1>
    explicit pair(const pair<_U0, _U1> &_other) {
      const auto &[d_a0, d_a1] =
          std::get<typename pair<_U0, _U1>::Pair0>(_other.v());
      d_v_ = Pair0{t_A(d_a0), t_B(d_a1)};
    }

    static pair<t_A, t_B> pair0(t_A a0, t_B a1) {
      return pair(Pair0{std::move(a0), std::move(a1)});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    const variant_t &v() const { return d_v_; }
  };

  template <typename T1, typename T2, typename T3, MapsTo<T3, T1, T2> F0>
  static T3 pair_rect(F0 &&f, const pair<T1, T2> &p) {
    const auto &[d_a0, d_a1] = std::get<typename pair<T1, T2>::Pair0>(p.v());
    return f(d_a0, d_a1);
  }

  template <typename T1, typename T2, typename T3, MapsTo<T3, T1, T2> F0>
  static T3 pair_rec(F0 &&f, const pair<T1, T2> &p) {
    const auto &[d_a0, d_a1] = std::get<typename pair<T1, T2>::Pair0>(p.v());
    return f(d_a0, d_a1);
  }

  static inline const pair<unsigned int, std::monostate> pair_with_unit =
      pair<unsigned int, std::monostate>::pair0(3u, std::monostate{});
  static inline const pair<std::monostate, std::monostate> unit_pair =
      pair<std::monostate, std::monostate>::pair0(std::monostate{},
                                                  std::monostate{});
  static void unit_to_unit(std::monostate u);

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
