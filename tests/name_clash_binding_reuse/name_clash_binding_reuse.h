#ifndef INCLUDED_NAME_CLASH_BINDING_REUSE
#define INCLUDED_NAME_CLASH_BINDING_REUSE

#include <type_traits>
#include <variant>

struct NameClashBindingReuse {
  struct pair_nat {
    // DATA
    uint64_t a0;
    uint64_t a1;

    // ACCESSORS
    pair_nat clone() const { return {a0, a1}; }

    // CREATORS
    static pair_nat mkpairnat(uint64_t a0, uint64_t a1) { return {a0, a1}; }

    pair_nat flat_combine(const pair_nat &p2) const {
      const auto &[a0, a2] = *this;
      const auto &[a00, a10] = p2;
      return pair_nat::mkpairnat((a0 + a00), (a2 + a10));
    }

    uint64_t add_pairs_let(const pair_nat &p2) const {
      uint64_t sum1 = [&]() {
        const auto &[a0, a1] = *this;
        return (a0 + a1);
      }();
      uint64_t sum2 = [&]() {
        const auto &[a00, a10] = p2;
        return (a00 + a10);
      }();
      return (sum1 + sum2);
    }

    uint64_t add_pairs(const pair_nat &p2) const {
      const auto &[a0, a2] = *this;
      const auto &[a00, a10] = p2;
      return (((a0 + a2) + a00) + a10);
    }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &, uint64_t &>
    T1 pair_nat_rec(F0 &&f) const {
      const auto &[a0, a1] = *this;
      return f(a0, a1);
    }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &, uint64_t &>
    T1 pair_nat_rect(F0 &&f) const {
      const auto &[a0, a1] = *this;
      return f(a0, a1);
    }
  };

  struct triple_nat {
    // DATA
    uint64_t a0;
    uint64_t a1;
    uint64_t a2;

    // ACCESSORS
    triple_nat clone() const { return {a0, a1, a2}; }

    // CREATORS
    static triple_nat mktriplenat(uint64_t a0, uint64_t a1, uint64_t a2) {
      return {a0, a1, a2};
    }

    uint64_t cascade_and_match() const {
      const auto &_sv = this->cascade();
      const auto &[a0, a1] = _sv;
      return (a0 + a1);
    }

    pair_nat cascade() const {
      const auto &[a0, a1, a2] = *this;
      return pair_nat::mkpairnat((a0 + a1), a2);
    }

    uint64_t combine(const pair_nat &p) const {
      const auto &[a0, a1, a2] = *this;
      const auto &[a00, a10] = p;
      return ((((a0 + a1) + a2) + a00) + a10);
    }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &, uint64_t &,
                                     uint64_t &>
    T1 triple_nat_rec(F0 &&f) const {
      const auto &[a0, a1, a2] = *this;
      return f(a0, a1, a2);
    }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &, uint64_t &,
                                     uint64_t &>
    T1 triple_nat_rect(F0 &&f) const {
      const auto &[a0, a1, a2] = *this;
      return f(a0, a1, a2);
    }
  };
};

#endif // INCLUDED_NAME_CLASH_BINDING_REUSE
