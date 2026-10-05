#ifndef INCLUDED_GENERATED_MEMBER_NAME_COLLISION
#define INCLUDED_GENERATED_MEMBER_NAME_COLLISION

#include <cstdint>
#include <type_traits>
#include <variant>

struct GeneratedMemberNameCollision {
  struct boxed {
    // DATA
    uint64_t clone_0;
    uint64_t v_mut_1;

    // ACCESSORS
    boxed clone() const { return {clone_0, v_mut_1}; }

    // CREATORS
    static boxed box(uint64_t clone_0, uint64_t v_mut_1) {
      return {clone_0, v_mut_1};
    }

    uint64_t unbox() const {
      const auto &[clone_0, v_mut_1] = *this;
      return (clone_0 + v_mut_1);
    }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, const uint64_t &,
                                     const uint64_t &>
    T1 boxed_rec(F0 &&f) const {
      const auto &[clone_0, v_mut_1] = *this;
      return f(clone_0, v_mut_1);
    }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, const uint64_t &,
                                     const uint64_t &>
    T1 boxed_rect(F0 &&f) const {
      const auto &[clone_0, v_mut_1] = *this;
      return f(clone_0, v_mut_1);
    }
  };

  struct clone0 {
    // DATA
    uint64_t a0;

    // ACCESSORS
    clone0 clone() const { return {a0}; }

    // CREATORS
    static clone0 dup(uint64_t a0) { return {a0}; }

    uint64_t undup() const {
      const auto &[a0] = *this;
      return a0;
    }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, const uint64_t &>
    T1 clone_rec(F0 &&f) const {
      const auto &[a0] = *this;
      return f(a0);
    }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, const uint64_t &>
    T1 clone_rect(F0 &&f) const {
      const auto &[a0] = *this;
      return f(a0);
    }
  };

  static constexpr uint64_t boxed_sum = UINT64_C(3);
  static constexpr uint64_t clone_val = UINT64_C(4);
};

#endif // INCLUDED_GENERATED_MEMBER_NAME_COLLISION
