#ifndef INCLUDED_NAME_CLASH_LET_MATCH
#define INCLUDED_NAME_CLASH_LET_MATCH

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

struct NameClashLetMatch {
  /// Tests for variable name clashes between let-bindings and match bindings.
  struct either {
    // TYPES
    struct Left {
      unsigned int d_a0;
    };

    struct Right {
      unsigned int d_a0;
    };

    using variant_t = std::variant<Left, Right>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    either() {}

    explicit either(Left _v) : d_v_(std::move(_v)) {}

    explicit either(Right _v) : d_v_(std::move(_v)) {}

    either(const either &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    either(either &&_other) : d_v_(std::move(_other.d_v_)) {}

    either &operator=(const either &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    either &operator=(either &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) either clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<Left>(_sv.v())) {
        const auto &[d_a0] = std::get<Left>(_sv.v());
        return either(Left{d_a0});
      } else {
        const auto &[d_a0] = std::get<Right>(_sv.v());
        return either(Right{d_a0});
      }
    }

    // CREATORS
    __attribute__((pure)) static either left(unsigned int a0) {
      return either(Left{std::move(a0)});
    }

    __attribute__((pure)) static either right(unsigned int a0) {
      return either(Right{std::move(a0)});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    /// Deeply nested let-match-let-match chain
    __attribute__((pure)) unsigned int deep_let_match(const either &e2,
                                                      const either &e3) const {
      unsigned int a = [&]() {
        auto &&_sv = *(this);
        if (std::holds_alternative<typename either::Left>(_sv.v())) {
          const auto &[d_a0] = std::get<typename either::Left>(_sv.v());
          return d_a0;
        } else {
          const auto &[d_a0] = std::get<typename either::Right>(_sv.v());
          return d_a0;
        }
      }();
      unsigned int b = [&]() {
        if (std::holds_alternative<typename either::Left>(e2.v())) {
          const auto &[d_a00] = std::get<typename either::Left>(e2.v());
          unsigned int z = [&]() {
            if (std::holds_alternative<typename either::Left>(e3.v())) {
              const auto &[d_a01] = std::get<typename either::Left>(e3.v());
              return d_a01;
            } else {
              const auto &[d_a01] = std::get<typename either::Right>(e3.v());
              return d_a01;
            }
          }();
          return (d_a00 + z);
        } else {
          const auto &[d_a00] = std::get<typename either::Right>(e2.v());
          return d_a00;
        }
      }();
      return (a + b);
    }

    /// Two either values matched in sequence, same field names.
    __attribute__((pure)) unsigned int two_eithers(const either &e2) const {
      unsigned int v1 = [&]() {
        auto &&_sv = *(this);
        if (std::holds_alternative<typename either::Left>(_sv.v())) {
          const auto &[d_a0] = std::get<typename either::Left>(_sv.v());
          return d_a0;
        } else {
          const auto &[d_a0] = std::get<typename either::Right>(_sv.v());
          return (d_a0 * 2u);
        }
      }();
      unsigned int v2 = [&]() {
        if (std::holds_alternative<typename either::Left>(e2.v())) {
          const auto &[d_a00] = std::get<typename either::Left>(e2.v());
          return d_a00;
        } else {
          const auto &[d_a00] = std::get<typename either::Right>(e2.v());
          return (d_a00 * 3u);
        }
      }();
      return (v1 + v2);
    }

    /// Match binding used in a nested let that shadows.
    __attribute__((pure)) unsigned int match_then_let() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename either::Left>(_sv.v())) {
        const auto &[d_a0] = std::get<typename either::Left>(_sv.v());
        return (d_a0 + 1u);
      } else {
        const auto &[d_a0] = std::get<typename either::Right>(_sv.v());
        return d_a0;
      }
    }

    template <typename T1, MapsTo<T1, unsigned int> F0,
              MapsTo<T1, unsigned int> F1>
    T1 either_rec(F0 &&f, F1 &&f0) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename either::Left>(_sv.v())) {
        const auto &[d_a0] = std::get<typename either::Left>(_sv.v());
        return f(d_a0);
      } else {
        const auto &[d_a0] = std::get<typename either::Right>(_sv.v());
        return f0(d_a0);
      }
    }

    template <typename T1, MapsTo<T1, unsigned int> F0,
              MapsTo<T1, unsigned int> F1>
    T1 either_rect(F0 &&f, F1 &&f0) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename either::Left>(_sv.v())) {
        const auto &[d_a0] = std::get<typename either::Left>(_sv.v());
        return f(d_a0);
      } else {
        const auto &[d_a0] = std::get<typename either::Right>(_sv.v());
        return f0(d_a0);
      }
    }
  };

  struct triple {
    // TYPES
    struct MkTriple {
      unsigned int d_a0;
      unsigned int d_a1;
      unsigned int d_a2;
    };

    using variant_t = std::variant<MkTriple>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    triple() {}

    explicit triple(MkTriple _v) : d_v_(std::move(_v)) {}

    triple(const triple &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    triple(triple &&_other) : d_v_(std::move(_other.d_v_)) {}

    triple &operator=(const triple &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    triple &operator=(triple &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) triple clone() const {
      auto &&_sv = *(this);
      const auto &[d_a0, d_a1, d_a2] = std::get<MkTriple>(_sv.v());
      return triple(MkTriple{d_a0, d_a1, d_a2});
    }

    // CREATORS
    __attribute__((pure)) static triple
    mktriple(unsigned int a0, unsigned int a1, unsigned int a2) {
      return triple(MkTriple{std::move(a0), std::move(a1), std::move(a2)});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    /// Match on a triple, then match on an either, same-ish names
    __attribute__((pure)) unsigned int
    triple_then_either(const either &e) const {
      auto &&_sv = *(this);
      const auto &[d_a0, d_a1, d_a2] =
          std::get<typename triple::MkTriple>(_sv.v());
      unsigned int from_either = [&]() {
        if (std::holds_alternative<typename either::Left>(e.v())) {
          const auto &[d_a00] = std::get<typename either::Left>(e.v());
          return d_a00;
        } else {
          const auto &[d_a00] = std::get<typename either::Right>(e.v());
          return d_a00;
        }
      }();
      return (((d_a0 + d_a1) + d_a2) + from_either);
    }

    template <typename T1,
              MapsTo<T1, unsigned int, unsigned int, unsigned int> F0>
    T1 triple_rec(F0 &&f) const {
      auto &&_sv = *(this);
      const auto &[d_a0, d_a1, d_a2] =
          std::get<typename triple::MkTriple>(_sv.v());
      return f(d_a0, d_a1, d_a2);
    }

    template <typename T1,
              MapsTo<T1, unsigned int, unsigned int, unsigned int> F0>
    T1 triple_rect(F0 &&f) const {
      auto &&_sv = *(this);
      const auto &[d_a0, d_a1, d_a2] =
          std::get<typename triple::MkTriple>(_sv.v());
      return f(d_a0, d_a1, d_a2);
    }
  };

  /// Variable name 'a' used in both let and match binding.
  __attribute__((pure)) static unsigned int let_shadows_match(const either &e);
  /// Match where the same variable name is used in multiple branches
  __attribute__((pure)) static unsigned int same_name_branches(const either &e,
                                                               const triple &t);
};

#endif // INCLUDED_NAME_CLASH_LET_MATCH
