#include "rocq_bug_7228.h"

RocqBug7228::t_of RocqBug7228::v_of(const RocqBug7228::data &d) {
  const auto &[t] = d;
  return t;
}
