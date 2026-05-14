#ifndef INCLUDED_QUALIFIED_RECORD_SHADOW
#define INCLUDED_QUALIFIED_RECORD_SHADOW

#include <memory>
#include <optional>
#include <type_traits>

struct QualifiedRecordShadow {
  struct Shadow {
    unsigned int value;
  };

  static Shadow bump(const Shadow &x);
  static inline const Shadow t = bump(Shadow{1u});
};

#endif // INCLUDED_QUALIFIED_RECORD_SHADOW
