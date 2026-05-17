#ifndef INCLUDED_TODO_IOTA_COMPLEX_PATTERN
#define INCLUDED_TODO_IOTA_COMPLEX_PATTERN

#include <type_traits>
#include <utility>
#include <variant>

struct TodoIotaComplexPattern {
  template <typename A, typename B, typename C> struct Triple {
    // TYPES
    struct MkTriple {
      A a0;
      B a1;
      C a2;
    };

    using variant_t = std::variant<MkTriple>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    Triple() {}

    explicit Triple(MkTriple _v) : v_(std::move(_v)) {}

    Triple(const Triple<A, B, C> &_other) : v_(std::move(_other.clone().v_)) {}

    Triple(Triple<A, B, C> &&_other) : v_(std::move(_other.v_)) {}

    Triple<A, B, C> &operator=(const Triple<A, B, C> &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    Triple<A, B, C> &operator=(Triple<A, B, C> &&_other) {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    Triple<A, B, C> clone() const {
      const auto &[a0, a1, a2] = std::get<MkTriple>(this->v());
      return Triple<A, B, C>(MkTriple{a0, a1, a2});
    }

    // CREATORS
    template <typename _U0, typename _U1, typename _U2>
    explicit Triple(const Triple<_U0, _U1, _U2> &_other) {
      const auto &[a0, a1, a2] =
          std::get<typename Triple<_U0, _U1, _U2>::MkTriple>(_other.v());
      this->v_ = MkTriple{A(a0), B(a1), C(a2)};
    }

    static Triple<A, B, C> mktriple(A a0, B a1, C a2) {
      return Triple(MkTriple{std::move(a0), std::move(a1), std::move(a2)});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename T2, typename T3, typename T4, typename F0>
    requires std::is_invocable_r_v<T4, F0 &, T1 &, T2 &, T3 &>
  static T4 Triple_rect(F0 &&f, const Triple<T1, T2, T3> &t) {
    const auto &[a0, a1, a2] =
        std::get<typename Triple<T1, T2, T3>::MkTriple>(t.v());
    return f(a0, a1, a2);
  }

  template <typename T1, typename T2, typename T3, typename T4, typename F0>
    requires std::is_invocable_r_v<T4, F0 &, T1 &, T2 &, T3 &>
  static T4 Triple_rec(F0 &&f, const Triple<T1, T2, T3> &t) {
    const auto &[a0, a1, a2] =
        std::get<typename Triple<T1, T2, T3>::MkTriple>(t.v());
    return f(a0, a1, a2);
  }

  static unsigned int
  sum_triple(const Triple<unsigned int, unsigned int, unsigned int> &t);

  template <typename T1, typename T2, typename T3>
  static Triple<T2, T3, T1> rotate_triple(const Triple<T1, T2, T3> &t) {
    const auto &[a0, a1, a2] =
        std::get<typename Triple<T1, T2, T3>::MkTriple>(t.v());
    return Triple<T2, T3, T1>::mktriple(a1, a2, a0);
  }

  static inline const unsigned int test1 = sum_triple(
      Triple<unsigned int, unsigned int, unsigned int>::mktriple(1u, 2u, 3u));
  static inline const Triple<bool, unsigned int, unsigned int> test2 =
      rotate_triple<unsigned int, bool, unsigned int>(
          Triple<unsigned int, bool, unsigned int>::mktriple(10u, true, 20u));
};

#endif // INCLUDED_TODO_IOTA_COMPLEX_PATTERN
