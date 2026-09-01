#include "loopify_frame_receiver_ptr.h"

String LoopifyFrameReceiverPtr::f(const List<String> &l) {
  return String::string0(
             Ascii::ascii0(false, false, true, true, false, true, false, false),
             String::emptystring())
      .concat(l);
}
