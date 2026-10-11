#include "noloopify_method.h"

NoloopifyMethod::reader NoloopifyMethod::read_with(NoloopifyMethod::tree t) {
  return reader::reader0(
      [=, t = std::move(t)](uint64_t x) { return (x + t.size()); });
}
