#ifndef INCLUDED_NAME_CLASH_BINDING_REUSE
#define INCLUDED_NAME_CLASH_BINDING_REUSE

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

struct NameClashBindingReuse {
  /// Test: structured binding names (d_a0 etc.) reused across matches.
  /// Particularly tricky when matches are NOT wrapped in IIFEs
  /// (i.e. statement-position matches vs expression-position matches).
  struct pair_nat {
    // TYPES
    struct MkPairNat {
      unsigned int d_a0;
      unsigned int d_a1;
    };

    using variant_t = std::variant<MkPairNat>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    explicit pair_nat(MkPairNat _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<pair_nat> mkpairnat(unsigned int a0,
                                               unsigned int a1) {
      return std::make_shared<pair_nat>(
          MkPairNat{std::move(a0), std::move(a1)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    /// Single-constructor match inside single-constructor match.
    /// Neither needs an if guard, just structured bindings.
    /// Could be tricky if both are in the same block without scoping.
    std::shared_ptr<pair_nat>
    flat_combine(const std::shared_ptr<pair_nat> &p2) const {
      const auto &[d_a0, d_a1] =
          std::get<typename pair_nat::MkPairNat>(this->v());
      const auto &[d_a00, d_a10] =
          std::get<typename pair_nat::MkPairNat>(p2->v());
      return pair_nat::mkpairnat((d_a0 + d_a00), (d_a1 + d_a10));
    }

    /// Same but as let-bindings (each match is an expression → IIFE).
    __attribute__((pure)) unsigned int
    add_pairs_let(const std::shared_ptr<pair_nat> &p2) const {
      unsigned int sum1 = [&]() {
        const auto &[d_a0, d_a1] =
            std::get<typename pair_nat::MkPairNat>(this->v());
        return (d_a0 + d_a1);
      }();
      unsigned int sum2 = [&]() {
        const auto &[d_a00, d_a10] =
            std::get<typename pair_nat::MkPairNat>(p2->v());
        return (d_a00 + d_a10);
      }();
      return (sum1 + sum2);
    }

    /// Two matches in sequence, both on pair_nat.
    /// Both generate d_a0, d_a1 structured bindings.
    __attribute__((pure)) unsigned int
    add_pairs(const std::shared_ptr<pair_nat> &p2) const {
      const auto &[d_a0, d_a1] =
          std::get<typename pair_nat::MkPairNat>(this->v());
      const auto &[d_a00, d_a10] =
          std::get<typename pair_nat::MkPairNat>(p2->v());
      return (((d_a0 + d_a1) + d_a00) + d_a10);
    }

    template <typename T1, MapsTo<T1, unsigned int, unsigned int> F0>
    T1 pair_nat_rec(F0 &&f) const {
      const auto &[d_a0, d_a1] =
          std::get<typename pair_nat::MkPairNat>(this->v());
      return f(d_a0, d_a1);
    }

    template <typename T1, MapsTo<T1, unsigned int, unsigned int> F0>
    T1 pair_nat_rect(F0 &&f) const {
      const auto &[d_a0, d_a1] =
          std::get<typename pair_nat::MkPairNat>(this->v());
      return f(d_a0, d_a1);
    }
  };

  struct triple_nat {
    // TYPES
    struct MkTripleNat {
      unsigned int d_a0;
      unsigned int d_a1;
      unsigned int d_a2;
    };

    using variant_t = std::variant<MkTripleNat>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    explicit triple_nat(MkTripleNat _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<triple_nat>
    mktriplenat(unsigned int a0, unsigned int a1, unsigned int a2) {
      return std::make_shared<triple_nat>(
          MkTripleNat{std::move(a0), std::move(a1), std::move(a2)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    __attribute__((pure)) unsigned int cascade_and_match() const {
      auto &&_sv = this->cascade();
      const auto &[d_a0, d_a1] =
          std::get<typename pair_nat::MkPairNat>(_sv->v());
      return (d_a0 + d_a1);
    }

    /// Match where the binding variable is used as scrutinee of another match
    std::shared_ptr<pair_nat> cascade() const {
      const auto &[d_a0, d_a1, d_a2] =
          std::get<typename triple_nat::MkTripleNat>(this->v());
      return pair_nat::mkpairnat((d_a0 + d_a1), d_a2);
    }

    /// Nested match: outer match on triple, inner match on pair.
    /// Both have d_a0, d_a1; inner should get d_a00, d_a10.
    __attribute__((pure)) unsigned int
    combine(const std::shared_ptr<pair_nat> &p) const {
      const auto &[d_a0, d_a1, d_a2] =
          std::get<typename triple_nat::MkTripleNat>(this->v());
      const auto &[d_a00, d_a10] =
          std::get<typename pair_nat::MkPairNat>(p->v());
      return ((((d_a0 + d_a1) + d_a2) + d_a00) + d_a10);
    }

    template <typename T1,
              MapsTo<T1, unsigned int, unsigned int, unsigned int> F0>
    T1 triple_nat_rec(F0 &&f) const {
      const auto &[d_a0, d_a1, d_a2] =
          std::get<typename triple_nat::MkTripleNat>(this->v());
      return f(d_a0, d_a1, d_a2);
    }

    template <typename T1,
              MapsTo<T1, unsigned int, unsigned int, unsigned int> F0>
    T1 triple_nat_rect(F0 &&f) const {
      const auto &[d_a0, d_a1, d_a2] =
          std::get<typename triple_nat::MkTripleNat>(this->v());
      return f(d_a0, d_a1, d_a2);
    }
  };
};

#endif // INCLUDED_NAME_CLASH_BINDING_REUSE
