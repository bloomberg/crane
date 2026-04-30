#ifndef INCLUDED_LOOPIFY_CLASSICS
#define INCLUDED_LOOPIFY_CLASSICS

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

struct LoopifyClassics {
  static unsigned int factorial(const unsigned int &n);
  static unsigned int fib(const unsigned int &n);
  static unsigned int ack_fuel(const unsigned int &fuel, const unsigned int &m,
                               const unsigned int &n);
  static unsigned int ack(const unsigned int &m, const unsigned int &n);
  static unsigned int binomial_fuel(const unsigned int &fuel,
                                    const unsigned int &n,
                                    const unsigned int &k);
  static unsigned int binomial(const unsigned int &n, const unsigned int &k);
  static unsigned int pascal_fuel(const unsigned int &fuel,
                                  const unsigned int &row,
                                  const unsigned int &col);
  static unsigned int pascal(const unsigned int &row, const unsigned int &col);
  static unsigned int gcd_fuel(const unsigned int &fuel, unsigned int a,
                               const unsigned int &b);
  static unsigned int gcd(const unsigned int &a, const unsigned int &b);
  static unsigned int power(const unsigned int &base, const unsigned int &exp);
  static unsigned int sum_to(const unsigned int &n);
  static unsigned int sum_squares(const unsigned int &n);
};

#endif // INCLUDED_LOOPIFY_CLASSICS
