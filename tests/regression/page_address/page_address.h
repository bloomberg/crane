#ifndef INCLUDED_PAGE_ADDRESS
#define INCLUDED_PAGE_ADDRESS

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

struct PageAddress {
  __attribute__((pure)) static unsigned int
  addr12_of_nat(const unsigned int &n);
  __attribute__((pure)) static unsigned int page_of(const unsigned int &p);
  __attribute__((pure)) static unsigned int page_base(const unsigned int &p);
  __attribute__((pure)) static unsigned int
  branch_target(const unsigned int &pc, const unsigned int &off);
  static inline const unsigned int p_small = 777u;
  static inline const unsigned int p_same = 600u;
  static inline const unsigned int p_cross_254 = 254u;
  static inline const unsigned int p_cross_255 = 255u;
  static inline const unsigned int page_base_777 = page_base(777u);
  static inline const unsigned int branch_example = branch_target(100u, 42u);
};

#endif // INCLUDED_PAGE_ADDRESS
