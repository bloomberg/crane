#include <simple_lambda_field_capture.h>

/// Dummy use of tag.
SimpleLambdaFieldCapture::tag SimpleLambdaFieldCapture::mk_tag(unsigned int n) {
  return tag::mktag(n);
}
