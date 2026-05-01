#include <list_self_deep_copy.h>

std::pair<ListSelfDeepCopy::chain, ListSelfDeepCopy::chain>
ListSelfDeepCopy::dup_chain(ListSelfDeepCopy::chain c) {
  return std::make_pair(c, c);
}
