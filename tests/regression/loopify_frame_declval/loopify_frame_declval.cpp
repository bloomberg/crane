#include "loopify_frame_declval.h"

List<std::pair<uint64_t, uint64_t>>
LoopifyFrameDeclval::g(const List<uint64_t> &l) {
  return l.template list_prod<uint64_t>(l);
}
