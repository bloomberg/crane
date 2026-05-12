#ifndef INCLUDED_NESTED_RECORD_UPDATE_QUAL
#define INCLUDED_NESTED_RECORD_UPDATE_QUAL

#include <memory>
#include <optional>
#include <type_traits>

struct NestedRecordUpdateQual {
  struct Shadow {
    unsigned int value;
  };

  static Shadow bump(const Shadow &x);
  static inline const Shadow t = bump(Shadow(1u));
};

#endif // INCLUDED_NESTED_RECORD_UPDATE_QUAL
