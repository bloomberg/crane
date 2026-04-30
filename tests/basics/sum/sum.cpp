#include <sum.h>

unsigned int
Sum::either_to_nat(const Sum::either<unsigned int, unsigned int> &e) {
  if (std::holds_alternative<
          typename Sum::either<unsigned int, unsigned int>::Left>(e.v())) {
    const auto &[d_a0] =
        std::get<typename Sum::either<unsigned int, unsigned int>::Left>(e.v());
    return d_a0;
  } else {
    const auto &[d_a0] =
        std::get<typename Sum::either<unsigned int, unsigned int>::Right>(
            e.v());
    return d_a0;
  }
}
