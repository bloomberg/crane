#include <move_capture_reuse.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) List<List<unsigned int>>
MoveCaptureReuse::prefix_each(List<unsigned int> prefix,
                              const List<List<unsigned int>> &xss) {
  return xss.template map<List<unsigned int>>(
      [=](const List<unsigned int> &xs) mutable { return prefix.app(xs); });
}
