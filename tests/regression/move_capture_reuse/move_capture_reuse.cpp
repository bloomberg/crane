#include <move_capture_reuse.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
MoveCaptureReuse::prefix_each(
    std::shared_ptr<List<unsigned int>> prefix,
    const std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> &xss) {
  return xss->template map<std::shared_ptr<List<unsigned int>>>(
      [=](const std::shared_ptr<List<unsigned int>> &xs) mutable {
        return prefix->app(xs);
      });
}
