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
      unsigned int a0;
    };

    struct Right {
      unsigned int a0;
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

    either(const either &_other) : v_(std::move(_other.clone().v_)) {}

    either(either &&_other) : v_(std::move(_other.v_)) {}

    either &operator=(const either &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    either &operator=(either &&_other) {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    either clone() const {
      if (std::holds_alternative<Left>(this->v())) {
        const auto &[a0] = std::get<Left>(this->v());
        return either(Left{a0});
      } else {
        const auto &[a0] = std::get<Right>(this->v());
        return either(Right{a0});
      }
    }

    // CREATORS
    static either left(unsigned int a0) { return either(Left{a0}); }

    static either right(unsigned int a0) { return either(Right{a0}); }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    /// Deeply nested let-match-let-match chain
    unsigned int deep_let_match(const either &e2, const either &e3) const {
      unsigned int a = [&]() {
        if (std::holds_alternative<typename either::Left>(this->v())) {
          const auto &[a0] = std::get<typename either::Left>(this->v());
          return a0;
        } else {
          const auto &[a0] = std::get<typename either::Right>(this->v());
          return a0;
        }
      }();
      unsigned int b = [&]() {
        if (std::holds_alternative<typename either::Left>(e2.v())) {
          const auto &[a00] = std::get<typename either::Left>(e2.v());
          unsigned int z = [&]() {
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
    unsigned int two_eithers(const either &e2) const {
      unsigned int v1 = [&]() {
        if (std::holds_alternative<typename either::Left>(this->v())) {
          const auto &[a0] = std::get<typename either::Left>(this->v());
          return a0;
        } else {
          const auto &[a0] = std::get<typename either::Right>(this->v());
          return (a0 * 2u);
        }
      }();
      unsigned int v2 = [&]() {
        if (std::holds_alternative<typename either::Left>(e2.v())) {
          const auto &[a00] = std::get<typename either::Left>(e2.v());
          return a00;
        } else {
          const auto &[a00] = std::get<typename either::Right>(e2.v());
          return (a00 * 3u);
        }
      }();
      return (v1 + v2);
    }

    /// Match binding used in a nested let that shadows.
    unsigned int match_then_let() const {
      if (std::holds_alternative<typename either::Left>(this->v())) {
        const auto &[a0] = std::get<typename either::Left>(this->v());
        return (a0 + 1u);
      } else {
        const auto &[a0] = std::get<typename either::Right>(this->v());
        return a0;
      }
    }

    template <typename T1, typename F0, typename F1>
      requires std::is_invocable_r_v<T1, F0 &, unsigned int &> &&
               std::is_invocable_r_v<T1, F1 &, unsigned int &>
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
      requires std::is_invocable_r_v<T1, F0 &, unsigned int &> &&
               std::is_invocable_r_v<T1, F1 &, unsigned int &>
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
    // TYPES
    struct MkTriple {
      unsigned int a0;
      unsigned int a1;
      unsigned int a2;
    };

    using variant_t = std::variant<MkTriple>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    triple() {}

    explicit triple(MkTriple _v) : v_(std::move(_v)) {}

    triple(const triple &_other) : v_(std::move(_other.clone().v_)) {}

    triple(triple &&_other) : v_(std::move(_other.v_)) {}

    triple &operator=(const triple &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    triple &operator=(triple &&_other) {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    triple clone() const {
      const auto &[a0, a1, a2] = std::get<MkTriple>(this->v());
      return triple(MkTriple{a0, a1, a2});
    }

    // CREATORS
    static triple mktriple(unsigned int a0, unsigned int a1, unsigned int a2) {
      return triple(MkTriple{a0, a1, a2});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    /// Match on a triple, then match on an either, same-ish names
    unsigned int triple_then_either(const either &e) const {
      const auto &[a0, a1, a2] = std::get<typename triple::MkTriple>(this->v());
      unsigned int from_either = [&]() {
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
      requires std::is_invocable_r_v<T1, F0 &, unsigned int &, unsigned int &,
                                     unsigned int &>
    T1 triple_rec(F0 &&f) const {
      const auto &[a0, a1, a2] = std::get<typename triple::MkTriple>(this->v());
      return f(a0, a1, a2);
    }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, unsigned int &, unsigned int &,
                                     unsigned int &>
    T1 triple_rect(F0 &&f) const {
      const auto &[a0, a1, a2] = std::get<typename triple::MkTriple>(this->v());
      return f(a0, a1, a2);
    }
  };

  /// Variable name 'a' used in both let and match binding.
  static unsigned int let_shadows_match(const either &e);
  /// Match where the same variable name is used in multiple branches
  static unsigned int same_name_branches(const either &e, const triple &t);
};

#endif // INCLUDED_NAME_CLASH_LET_MATCH
