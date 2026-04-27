#ifndef INCLUDED_PROP_ERASURE
#define INCLUDED_PROP_ERASURE

#include <memory>
#include <optional>
#include <type_traits>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

struct PropErasure {
  __attribute__((pure)) static unsigned int with_proof_arg(unsigned int n);
  static inline const unsigned int use_proof = with_proof_arg(5u);
  static inline const unsigned int simple_value = 7u;
  __attribute__((pure)) static unsigned int
  add_with_proof(const unsigned int &_x0, const unsigned int &_x1);
  static inline const unsigned int test_add_proof = add_with_proof(3u, 4u);
  static inline const unsigned int test_use_proof = use_proof;
  static inline const unsigned int test_simple = simple_value;
};

#endif // INCLUDED_PROP_ERASURE
