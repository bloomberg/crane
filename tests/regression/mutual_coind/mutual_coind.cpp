#include <mutual_coind.h>

MutualCoind::streamA<unsigned int> MutualCoind::countA(const unsigned int n) {
  return streamA<unsigned int>::lazy_(
      [=]() mutable -> MutualCoind::streamA<unsigned int> {
        return streamA<unsigned int>::consa(n, countB((n + 1)));
      });
}

MutualCoind::streamB<unsigned int> MutualCoind::countB(const unsigned int n) {
  return streamB<unsigned int>::lazy_(
      [=]() mutable -> MutualCoind::streamB<unsigned int> {
        return streamB<unsigned int>::consb(n, countA((n + 1)));
      });
}
