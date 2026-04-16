#ifndef INCLUDED_QUALIFIED_RECORD_SHADOW
#define INCLUDED_QUALIFIED_RECORD_SHADOW

#include <memory>
#include <type_traits>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

struct QualifiedRecordShadow {
  struct Shadow {
    unsigned int value;
  };

  static std::shared_ptr<Shadow> bump(const std::shared_ptr<Shadow> &x);
  static inline const std::shared_ptr<Shadow> t =
      bump(std::make_shared<Shadow>(Shadow{1u}));
};

#endif // INCLUDED_QUALIFIED_RECORD_SHADOW
