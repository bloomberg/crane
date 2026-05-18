#include "mutual_coind.h"

MutualCoind::streamA<uint64_t> MutualCoind::countA(uint64_t n) {
  return streamA<uint64_t>::lazy_(
      [=]() mutable -> MutualCoind::streamA<uint64_t> {
        return streamA<uint64_t>::consa(n, countB((n + 1)));
      });
}

MutualCoind::streamB<uint64_t> MutualCoind::countB(uint64_t n) {
  return streamB<uint64_t>::lazy_(
      [=]() mutable -> MutualCoind::streamB<uint64_t> {
        return streamB<uint64_t>::consb(n, countA((n + 1)));
      });
}
