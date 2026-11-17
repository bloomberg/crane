#include <obj.h>
#include <ptr_word.h>

#include <cassert>

int main() {
  assert(PtrWord::sample == 3);

  auto t1 = PtrWord::tree::node(PtrWord::tree::leaf(), PtrWord::tree::leaf());
  auto t2 = PtrWord::tree::node(t1, PtrWord::tree::leaf());
  auto b1 = crane::shared_box<PtrWord::tree>::make(t1);
  auto b2 = crane::shared_box<PtrWord::tree>::make(t2);
  b1 = b2;
  assert(PtrWord::size(*b1) == 3);
  b2 = nullptr;

  crane::obj o1(t1);
  crane::obj o2(t2);
  o1.swap(o2);
  assert(PtrWord::size(crane::any_cast<const PtrWord::tree &>(o1)) == 3);
  assert(PtrWord::size(crane::any_cast<const PtrWord::tree &>(o2)) == 2);
  return 0;
}
