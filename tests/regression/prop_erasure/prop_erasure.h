#include <algorithm>
#include <any>
#include <functional>
#include <iostream>
#include <memory>
#include <stdexcept>
#include <string>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

struct PropErasure {
  static unsigned int with_proof_arg(const unsigned int n);

  static inline const unsigned int use_proof = with_proof_arg(5u);

  static inline const unsigned int simple_value = 7u;

  static unsigned int add_with_proof(const unsigned int, const unsigned int);

  static inline const unsigned int test_add_proof = add_with_proof(3u, 4u);

  static inline const unsigned int test_use_proof = use_proof;

  static inline const unsigned int test_simple = simple_value;
};
