#ifndef INCLUDED_ROCQ_BUG_4709
#define INCLUDED_ROCQ_BUG_4709

#include <any>

struct RocqBug4709 {
  enum class T { FOO };
  using foo = std::any;
  using ty = uint64_t;
  static inline const ty check = UINT64_C(42);
};

#endif // INCLUDED_ROCQ_BUG_4709
