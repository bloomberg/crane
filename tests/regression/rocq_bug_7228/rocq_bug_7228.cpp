#include <rocq_bug_7228.h>

__attribute__((pure)) RocqBug7228::t_of
RocqBug7228::v_of(const RocqBug7228::data &d) {
  const auto &[d_t] = std::get<typename RocqBug7228::data::Data0>(d.v());
  return d_t;
}
