#include "loopify_self_template_args.h"

List::list<uint64_t>
LoopifySelfTemplateArgs::rm(const List::list<uint64_t> &l) {
  return List::template remove<uint64_t>(
      [](uint64_t _x0, uint64_t _x1) -> bool { return _x0 == _x1; },
      UINT64_C(2), l);
}
