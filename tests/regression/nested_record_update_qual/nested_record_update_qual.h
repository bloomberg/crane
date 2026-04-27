#ifndef INCLUDED_NESTED_RECORD_UPDATE_QUAL
#define INCLUDED_NESTED_RECORD_UPDATE_QUAL

#include <memory>
#include <optional>
#include <type_traits>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

struct NestedRecordUpdateQual {
  struct Shadow {
    unsigned int value;
  };

  __attribute__((pure)) static Shadow bump(const Shadow &x);
  static inline const Shadow t = bump(Shadow{1u});
};

#endif // INCLUDED_NESTED_RECORD_UPDATE_QUAL
