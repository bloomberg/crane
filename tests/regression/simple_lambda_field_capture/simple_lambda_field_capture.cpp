#include <simple_lambda_field_capture.h>

#include <functional>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

/// Dummy use of tag.
__attribute__((pure)) SimpleLambdaFieldCapture::tag
SimpleLambdaFieldCapture::mk_tag(unsigned int n) {
  return tag::mktag(n);
}
