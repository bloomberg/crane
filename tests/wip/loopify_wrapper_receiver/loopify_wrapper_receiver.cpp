#include "loopify_wrapper_receiver.h"

LoopifyWrapperReceiver::t LoopifyWrapperReceiver::mk(uint64_t n) {
  return t::l().build(n);
}
