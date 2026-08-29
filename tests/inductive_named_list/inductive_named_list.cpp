#include "inductive_named_list.h"

uint64_t InductiveNamedList::len(const InductiveNamedList::List_ &l) {
  if (std::holds_alternative<typename InductiveNamedList::List_::LNil>(l.v())) {
    return UINT64_C(0);
  } else {
    const auto &[a0, a1] =
        std::get<typename InductiveNamedList::List_::LCons>(l.v());
    return (len(*a1) + 1);
  }
}
