#ifndef INCLUDED_LOOPIFY_CLASSICS
#define INCLUDED_LOOPIFY_CLASSICS

#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

struct LoopifyClassics {
  __attribute__((pure)) static unsigned int factorial(const unsigned int n);
  __attribute__((pure)) static unsigned int fib(const unsigned int n);
  __attribute__((pure)) static unsigned int
  ack_fuel(const unsigned int fuel, const unsigned int m, const unsigned int n);
  __attribute__((pure)) static unsigned int ack(const unsigned int m,
                                                const unsigned int n);
  __attribute__((pure)) static unsigned int
  binomial_fuel(const unsigned int fuel, const unsigned int n,
                const unsigned int k);
  __attribute__((pure)) static unsigned int binomial(const unsigned int n,
                                                     const unsigned int k);
  __attribute__((pure)) static unsigned int pascal_fuel(const unsigned int fuel,
                                                        const unsigned int row,
                                                        const unsigned int col);
  __attribute__((pure)) static unsigned int pascal(const unsigned int row,
                                                   const unsigned int col);
  __attribute__((pure)) static unsigned int
  gcd_fuel(const unsigned int fuel, const unsigned int a, const unsigned int b);
  __attribute__((pure)) static unsigned int gcd(const unsigned int a,
                                                const unsigned int b);
  __attribute__((pure)) static unsigned int power(const unsigned int base,
                                                  const unsigned int exp);
  __attribute__((pure)) static unsigned int sum_to(const unsigned int n);
  __attribute__((pure)) static unsigned int sum_squares(const unsigned int n);
};

#endif // INCLUDED_LOOPIFY_CLASSICS
