#ifndef INCLUDED_TODO_ETA_EXPANSION_TAXIOM
#define INCLUDED_TODO_ETA_EXPANSION_TAXIOM

#include <type_traits>
#include <utility>
#include <variant>

struct TodoEtaExpansionTaxiom {
  template <typename t_A, typename t_B> struct Pair {
    // TYPES
    struct MkPair {
      t_A d_a0;
      t_B d_a1;
    };

    using variant_t = std::variant<MkPair>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    Pair() {}

    explicit Pair(MkPair _v) : d_v_(std::move(_v)) {}

    Pair(const Pair<t_A, t_B> &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    Pair(Pair<t_A, t_B> &&_other) : d_v_(std::move(_other.d_v_)) {}

    Pair<t_A, t_B> &operator=(const Pair<t_A, t_B> &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    Pair<t_A, t_B> &operator=(Pair<t_A, t_B> &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    Pair<t_A, t_B> clone() const {
      const auto &[d_a0, d_a1] = std::get<MkPair>(this->v());
      return Pair<t_A, t_B>(MkPair{d_a0, d_a1});
    }

    // CREATORS
    template <typename _U0, typename _U1>
    explicit Pair(const Pair<_U0, _U1> &_other) {
      const auto &[d_a0, d_a1] =
          std::get<typename Pair<_U0, _U1>::MkPair>(_other.v());
      this->d_v_ = MkPair{t_A(d_a0), t_B(d_a1)};
    }

    static Pair<t_A, t_B> mkpair(t_A a0, t_B a1) {
      return Pair(MkPair{std::move(a0), std::move(a1)});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    const variant_t &v() const { return d_v_; }
  };

  template <typename T1, typename T2, typename T3, typename F0>
    requires std::is_invocable_r_v<T3, F0 &, T1 &, T2 &>
  static T3 Pair_rect(F0 &&f, const Pair<T1, T2> &p) {
    const auto &[d_a0, d_a1] = std::get<typename Pair<T1, T2>::MkPair>(p.v());
    return f(d_a0, d_a1);
  }

  template <typename T1, typename T2, typename T3, typename F0>
    requires std::is_invocable_r_v<T3, F0 &, T1 &, T2 &>
  static T3 Pair_rec(F0 &&f, const Pair<T1, T2> &p) {
    const auto &[d_a0, d_a1] = std::get<typename Pair<T1, T2>::MkPair>(p.v());
    return f(d_a0, d_a1);
  }

  template <typename T1, typename T2>
  static Pair<T2, T1> swap_pair(const Pair<T1, T2> &p) {
    const auto &[d_a0, d_a1] = std::get<typename Pair<T1, T2>::MkPair>(p.v());
    return Pair<T2, T1>::mkpair(d_a1, d_a0);
  }

  template <typename T1, typename T2>
  static T1 fst_pair(const Pair<T1, T2> &p) {
    const auto &[d_a0, d_a1] = std::get<typename Pair<T1, T2>::MkPair>(p.v());
    return d_a0;
  }

  static inline const Pair<bool, unsigned int> test_swap =
      swap_pair<unsigned int, bool>(Pair<unsigned int, bool>::mkpair(3u, true));
  static inline const unsigned int test_fst =
      fst_pair<unsigned int, bool>(Pair<unsigned int, bool>::mkpair(42u, true));
};

#endif // INCLUDED_TODO_ETA_EXPANSION_TAXIOM
