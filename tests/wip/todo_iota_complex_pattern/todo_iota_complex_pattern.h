#ifndef INCLUDED_TODO_IOTA_COMPLEX_PATTERN
#define INCLUDED_TODO_IOTA_COMPLEX_PATTERN

#include <type_traits>
#include <utility>
#include <variant>

struct TodoIotaComplexPattern {
  template <typename t_A, typename t_B, typename t_C> struct Triple {
    // TYPES
    struct MkTriple {
      t_A d_a0;
      t_B d_a1;
      t_C d_a2;
    };

    using variant_t = std::variant<MkTriple>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    Triple() {}

    explicit Triple(MkTriple _v) : d_v_(std::move(_v)) {}

    Triple(const Triple<t_A, t_B, t_C> &_other)
        : d_v_(std::move(_other.clone().d_v_)) {}

    Triple(Triple<t_A, t_B, t_C> &&_other) : d_v_(std::move(_other.d_v_)) {}

    Triple<t_A, t_B, t_C> &operator=(const Triple<t_A, t_B, t_C> &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    Triple<t_A, t_B, t_C> &operator=(Triple<t_A, t_B, t_C> &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    Triple<t_A, t_B, t_C> clone() const {
      const auto &[d_a0, d_a1, d_a2] = std::get<MkTriple>(this->v());
      return Triple<t_A, t_B, t_C>(MkTriple{d_a0, d_a1, d_a2});
    }

    // CREATORS
    template <typename _U0, typename _U1, typename _U2>
    explicit Triple(const Triple<_U0, _U1, _U2> &_other) {
      const auto &[d_a0, d_a1, d_a2] =
          std::get<typename Triple<_U0, _U1, _U2>::MkTriple>(_other.v());
      this->d_v_ = MkTriple{t_A(d_a0), t_B(d_a1), t_C(d_a2)};
    }

    static Triple<t_A, t_B, t_C> mktriple(t_A a0, t_B a1, t_C a2) {
      return Triple(MkTriple{std::move(a0), std::move(a1), std::move(a2)});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    const variant_t &v() const { return d_v_; }
  };

  template <typename T1, typename T2, typename T3, typename T4, typename F0>
    requires std::is_invocable_r_v<T4, F0 &, T1 &, T2 &, T3 &>
  static T4 Triple_rect(F0 &&f, const Triple<T1, T2, T3> &t) {
    const auto &[d_a0, d_a1, d_a2] =
        std::get<typename Triple<T1, T2, T3>::MkTriple>(t.v());
    return f(d_a0, d_a1, d_a2);
  }

  template <typename T1, typename T2, typename T3, typename T4, typename F0>
    requires std::is_invocable_r_v<T4, F0 &, T1 &, T2 &, T3 &>
  static T4 Triple_rec(F0 &&f, const Triple<T1, T2, T3> &t) {
    const auto &[d_a0, d_a1, d_a2] =
        std::get<typename Triple<T1, T2, T3>::MkTriple>(t.v());
    return f(d_a0, d_a1, d_a2);
  }

  static unsigned int
  sum_triple(const Triple<unsigned int, unsigned int, unsigned int> &t);

  template <typename T1, typename T2, typename T3>
  static Triple<T2, T3, T1> rotate_triple(const Triple<T1, T2, T3> &t) {
    const auto &[d_a0, d_a1, d_a2] =
        std::get<typename Triple<T1, T2, T3>::MkTriple>(t.v());
    return Triple<T2, T3, T1>::mktriple(d_a1, d_a2, d_a0);
  }

  static inline const unsigned int test1 = sum_triple(
      Triple<unsigned int, unsigned int, unsigned int>::mktriple(1u, 2u, 3u));
  static inline const Triple<bool, unsigned int, unsigned int> test2 =
      rotate_triple<unsigned int, bool, unsigned int>(
          Triple<unsigned int, bool, unsigned int>::mktriple(10u, true, 20u));
};

#endif // INCLUDED_TODO_IOTA_COMPLEX_PATTERN
