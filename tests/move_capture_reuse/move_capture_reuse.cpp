#include "move_capture_reuse.h"

List<List<uint64_t>>
MoveCaptureReuse::prefix_each(const List<uint64_t> &prefix,
                              const List<List<uint64_t>> &xss) {
  return xss.template map<List<uint64_t>>(
      [=](const List<uint64_t> &xs) mutable { return prefix.app(xs); });
}
