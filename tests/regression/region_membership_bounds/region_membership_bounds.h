#ifndef INCLUDED_REGION_MEMBERSHIP_BOUNDS
#define INCLUDED_REGION_MEMBERSHIP_BOUNDS

#include <memory>
#include <optional>
#include <type_traits>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

struct RegionMembershipBounds {
  struct layout {
    unsigned int base_addr;
    unsigned int code_size;

    __attribute__((pure)) layout *operator->() { return this; }

    __attribute__((pure)) const layout *operator->() const { return this; }

    // ACCESSORS
    __attribute__((pure)) layout clone() const {
      return layout{(*(this)).base_addr, (*(this)).code_size};
    }
  };

  __attribute__((pure)) static bool addr_in_regionb(const unsigned int &addr,
                                                    const layout &l);
  static inline const unsigned int t = []() {
    return []() {
      layout l = layout{100u, 20u};
      return ([&]() -> unsigned int {
        if (addr_in_regionb(110u, l)) {
          return 1u;
        } else {
          return 0u;
        }
      }() + [&]() -> unsigned int {
        if (addr_in_regionb(121u, l)) {
          return 1u;
        } else {
          return 0u;
        }
      }());
    }();
  }();
};

#endif // INCLUDED_REGION_MEMBERSHIP_BOUNDS
