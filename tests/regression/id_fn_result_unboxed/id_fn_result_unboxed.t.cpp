#include <id_fn_result_unboxed.h>

#include <cassert>

int main() {
  using M = IdFnResultUnboxed;
  assert(M::as_value.length() == 1);
  assert(M::as_argument == 2);
  assert(M::as_receiver == 3);
  assert(M::as_number == 5);
  assert(M::dup_len == 2);
  assert(M::matched_nil == 7);
  assert(M::matched_head == 5);
  assert(M::stream_head == 9);
  return 0;
}
