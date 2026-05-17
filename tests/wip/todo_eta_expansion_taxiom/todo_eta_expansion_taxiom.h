#ifndef INCLUDED_TODO_ETA_EXPANSION_TAXIOM
#define INCLUDED_TODO_ETA_EXPANSION_TAXIOM

#include <type_traits>
#include <utility>
#include <variant>

struct TodoEtaExpansionTaxiom {
  template <typename A, typename B> struct Pair {
    // TYPES
    struct MkPair {
      A a0;
      B a1;
    };

    using variant_t = std::variant<MkPair>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    Pair() {}

    explicit Pair(MkPair _v) : v_(std::move(_v)) {}

    Pair(const Pair<A, B> &_other) : v_(std::move(_other.clone().v_)) {}

    Pair(Pair<A, B> &&_other) : v_(std::move(_other.v_)) {}

    Pair<A, B> &operator=(const Pair<A, B> &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    Pair<A, B> &operator=(Pair<A, B> &&_other) {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    Pair<A, B> clone() const {
      const auto &[a0, a1] = std::get<MkPair>(this->v());
      return Pair<A, B>(MkPair{a0, a1});
    }

    // CREATORS
    template <typename _U0, typename _U1>
    explicit Pair(const Pair<_U0, _U1> &_other) {
      const auto &[a0, a1] =
          std::get<typename Pair<_U0, _U1>::MkPair>(_other.v());
      this->v_ = MkPair{A(a0), B(a1)};
    }

    static Pair<A, B> mkpair(A a0, B a1) {
      return Pair(MkPair{std::move(a0), std::move(a1)});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename T2, typename T3, typename F0>
    requires std::is_invocable_r_v<T3, F0 &, T1 &, T2 &>
  static T3 Pair_rect(F0 &&f, const Pair<T1, T2> &p) {
    const auto &[a0, a1] = std::get<typename Pair<T1, T2>::MkPair>(p.v());
    return f(a0, a1);
  }

  template <typename T1, typename T2, typename T3, typename F0>
    requires std::is_invocable_r_v<T3, F0 &, T1 &, T2 &>
  static T3 Pair_rec(F0 &&f, const Pair<T1, T2> &p) {
    const auto &[a0, a1] = std::get<typename Pair<T1, T2>::MkPair>(p.v());
    return f(a0, a1);
  }

  template <typename T1, typename T2>
  static Pair<T2, T1> swap_pair(const Pair<T1, T2> &p) {
    const auto &[a0, a1] = std::get<typename Pair<T1, T2>::MkPair>(p.v());
    return Pair<T2, T1>::mkpair(a1, a0);
  }

  template <typename T1, typename T2>
  static T1 fst_pair(const Pair<T1, T2> &p) {
    const auto &[a0, a1] = std::get<typename Pair<T1, T2>::MkPair>(p.v());
    return a0;
  }

  static inline const Pair<bool, unsigned int> test_swap =
      swap_pair<unsigned int, bool>(Pair<unsigned int, bool>::mkpair(3u, true));
  static inline const unsigned int test_fst =
      fst_pair<unsigned int, bool>(Pair<unsigned int, bool>::mkpair(42u, true));
};

#endif // INCLUDED_TODO_ETA_EXPANSION_TAXIOM
