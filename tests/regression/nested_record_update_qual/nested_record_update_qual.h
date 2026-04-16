#ifndef INCLUDED_NESTED_RECORD_UPDATE_QUAL
#define INCLUDED_NESTED_RECORD_UPDATE_QUAL

#include <memory>
#include <type_traits>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

struct NestedRecordUpdateQual {
  struct Shadow {
    unsigned int value;
  };

  static std::shared_ptr<Shadow> bump(const std::shared_ptr<Shadow> &x);
  static inline const std::shared_ptr<Shadow> t =
      bump(std::make_shared<Shadow>(Shadow{1u}));
};

#endif // INCLUDED_NESTED_RECORD_UPDATE_QUAL
