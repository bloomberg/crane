#include <simple_lambda_field_capture.h>

#include <functional>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

/// Dummy use of tag.
std::shared_ptr<SimpleLambdaFieldCapture::tag>
SimpleLambdaFieldCapture::mk_tag(const unsigned int n) {
  return tag::mktag(n);
}
