#include <loopify_block_template_frame.h>

#include <cassert>
#include <cstdio>
#include <vector>

int main() {
  std::vector<uint64_t> got;
  List<uint64_t> l = LoopifyBlockTemplateFrame::doubles(3);
  const List<uint64_t> *p = &l;
  while (std::holds_alternative<List<uint64_t>::Cons>(p->v())) {
    const auto &c = std::get<List<uint64_t>::Cons>(p->v());
    got.push_back(c.a);
    p = c.l.get();
  }
  assert((got == std::vector<uint64_t>{6, 4, 2}));
  // Deep enough to need the loop.
  assert(std::holds_alternative<List<uint64_t>::Cons>(
      LoopifyBlockTemplateFrame::doubles(200000).v()));
  std::printf("loopify_block_template_frame: ok\n");
  return 0;
}
