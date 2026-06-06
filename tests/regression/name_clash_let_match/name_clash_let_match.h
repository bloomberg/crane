#ifndef INCLUDED_NAME_CLASH_LET_MATCH
#define INCLUDED_NAME_CLASH_LET_MATCH

#include <type_traits>
#include <utility>
#include <variant>

struct NameClashLetMatch {
  /// Tests for variable name clashes between let-bindings and match bindings.
  struct either {
    // TYPES
    struct Left {
      uint64_t a0;
    };

    struct Right {
      uint64_t a0;
    };

    using variant_t = std::variant<Left, Right>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    either() {}

    explicit either(Left _v) : v_(std::move(_v)) {}

    explicit either(Right _v) : v_(std::move(_v)) {}

    static either left(uint64_t a0) { return either(Left{a0}); }

    static either right(uint64_t a0) { return either(Right{a0}); }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    /// Deeply nested let-match-let-match chain
    uint64_t deep_let_match(const either &e2, const either &e3) const {
      uint64_t a = [&]() {
        if (std::holds_alternative<typename either::Left>(this->v())) {
          const auto &[a0] = std::get<typename either::Left>(this->v());
          return a0;
        } else {
          const auto &[a0] = std::get<typename either::Right>(this->v());
          return a0;
        }
      }();
      uint64_t b = [&]() {
        if (std::holds_alternative<typename either::Left>(e2.v())) {
          const auto &[a00] = std::get<typename either::Left>(e2.v());
          uint64_t z = [&]() {
            if (std::holds_alternative<typename either::Left>(e3.v())) {
              const auto &[a01] = std::get<typename either::Left>(e3.v());
              return a01;
            } else {
              const auto &[a01] = std::get<typename either::Right>(e3.v());
              return a01;
            }
          }();
          return (a00 + z);
        } else {
          const auto &[a00] = std::get<typename either::Right>(e2.v());
          return a00;
        }
      }();
      return (a + b);
    }

    /// Two either values matched in sequence, same field names.
    uint64_t two_eithers(const either &e2) const {
      uint64_t v1 = [&]() {
        if (std::holds_alternative<typename either::Left>(this->v())) {
          const auto &[a0] = std::get<typename either::Left>(this->v());
          return a0;
        } else {
          const auto &[a0] = std::get<typename either::Right>(this->v());
          return (a0 * UINT64_C(2));
        }
      }();
      uint64_t v2 = [&]() {
        if (std::holds_alternative<typename either::Left>(e2.v())) {
          const auto &[a00] = std::get<typename either::Left>(e2.v());
          return a00;
        } else {
          const auto &[a00] = std::get<typename either::Right>(e2.v());
          return (a00 * UINT64_C(3));
        }
      }();
      return (v1 + v2);
    }

    /// Match binding used in a nested let that shadows.
    uint64_t match_then_let() const {
      if (std::holds_alternative<typename either::Left>(this->v())) {
        const auto &[a0] = std::get<typename either::Left>(this->v());
        return (a0 + UINT64_C(1));
      } else {
        const auto &[a0] = std::get<typename either::Right>(this->v());
        return a0;
      }
    }

    template <typename T1, typename F0, typename F1>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F1 &, uint64_t &>
    T1 either_rec(F0 &&f, F1 &&f0) const {
      if (std::holds_alternative<typename either::Left>(this->v())) {
        const auto &[a0] = std::get<typename either::Left>(this->v());
        return f(a0);
      } else {
        const auto &[a0] = std::get<typename either::Right>(this->v());
        return f0(a0);
      }
    }

    template <typename T1, typename F0, typename F1>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F1 &, uint64_t &>
    T1 either_rect(F0 &&f, F1 &&f0) const {
      if (std::holds_alternative<typename either::Left>(this->v())) {
        const auto &[a0] = std::get<typename either::Left>(this->v());
        return f(a0);
      } else {
        const auto &[a0] = std::get<typename either::Right>(this->v());
        return f0(a0);
      }
    }
  };

  struct triple {
    // DATA
    uint64_t a0;
    uint64_t a1;
    uint64_t a2;

    // ACCESSORS
    triple clone() const { return {a0, a1, a2}; }

    // CREATORS
    static triple mktriple(uint64_t a0, uint64_t a1, uint64_t a2) {
      return {a0, a1, a2};
    }

    /// Match on a triple, then match on an either, same-ish names
    uint64_t triple_then_either(const either &e) const {
      const auto &[a0, a1, a2] = *this;
      uint64_t from_either = [&]() {
        if (std::holds_alternative<typename either::Left>(e.v())) {
          const auto &[a00] = std::get<typename either::Left>(e.v());
          return a00;
        } else {
          const auto &[a00] = std::get<typename either::Right>(e.v());
          return a00;
        }
      }();
      return (((a0 + a1) + a2) + from_either);
    }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &, uint64_t &,
                                     uint64_t &>
    T1 triple_rec(F0 &&f) const {
      const auto &[a0, a1, a2] = *this;
      return f(a0, a1, a2);
    }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &, uint64_t &,
                                     uint64_t &>
    T1 triple_rect(F0 &&f) const {
      const auto &[a0, a1, a2] = *this;
      return f(a0, a1, a2);
    }
  };

  /// Variable name 'a' used in both let and match binding.
  static uint64_t let_shadows_match(const either &e);
  /// Match where the same variable name is used in multiple branches
  static uint64_t same_name_branches(const either &e, const triple &t);
};

#endif // INCLUDED_NAME_CLASH_LET_MATCH
