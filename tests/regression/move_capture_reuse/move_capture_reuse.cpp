#include <move_capture_reuse.h>

List<List<unsigned int>>
MoveCaptureReuse::prefix_each(List<unsigned int> prefix,
                              const List<List<unsigned int>> &xss) {
  return xss.template map<List<unsigned int>>(
      [=](const List<unsigned int> &xs) mutable { return prefix.app(xs); });
}
