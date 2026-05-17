#ifndef INCLUDED_ROCQ_BUG_4709
#define INCLUDED_ROCQ_BUG_4709

#include <any>

struct RocqBug4709 {
  enum class T { FOO };
  using foo = std::any;
  using ty = unsigned int;
  static inline const ty check = 42u;
};

#endif // INCLUDED_ROCQ_BUG_4709
