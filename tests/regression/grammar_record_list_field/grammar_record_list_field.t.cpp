#include <grammar_record_list_field.h>
#include <iostream>

// The defect is in the generated header: the Doc action constructs the record
// `rec{ ... }` forwarding an erased std::deque<std::any> into the concrete
// std::deque<elt> field WITHOUT crane_container_cast, so the header does not
// even compile (no viable conversion). Merely referencing `entries` instantiates
// it. In the real PPM parser this is PPM.h's
//   no viable conversion from 'deque<std::any>' to 'deque<rgb_triple>'.
int main() {
  std::cout << "entries size = " << entries.size() << std::endl;
  return 0;
}
