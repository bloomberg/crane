#include <move_capture_reuse.h>

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
MoveCaptureReuse::prefix_each(
    std::shared_ptr<List<unsigned int>> prefix,
    const std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> &xss) {
  return xss->template map<std::shared_ptr<List<unsigned int>>>(
      [=](std::shared_ptr<List<unsigned int>> xs) mutable {
        return prefix->app(xs);
      });
}
