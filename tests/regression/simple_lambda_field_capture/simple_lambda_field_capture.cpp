#include "simple_lambda_field_capture.h"

/// Dummy use of tag.
SimpleLambdaFieldCapture::tag SimpleLambdaFieldCapture::mk_tag(uint64_t n) {
  return tag::mktag(n);
}
