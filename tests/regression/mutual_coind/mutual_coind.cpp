#include "mutual_coind.h"

MutualCoind::streamA<uint64_t> MutualCoind::countA(uint64_t n) {
  return streamA<uint64_t>::lazy_(
      [=]() -> typename MutualCoind::streamA<uint64_t>::ConsA {
        return {n, countB((n + 1))};
      });
}

MutualCoind::streamB<uint64_t> MutualCoind::countB(uint64_t n) {
  return streamB<uint64_t>::lazy_(
      [=]() -> typename MutualCoind::streamB<uint64_t>::ConsB {
        return {n, countA((n + 1))};
      });
}
