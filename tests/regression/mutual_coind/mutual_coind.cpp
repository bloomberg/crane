#include <mutual_coind.h>

__attribute__((pure)) MutualCoind::streamA<unsigned int>
MutualCoind::countA(unsigned int n) {
  return streamA<unsigned int>::lazy_(
      [=]() mutable -> MutualCoind::streamA<unsigned int> {
        return streamA<unsigned int>::consa(n, countB((n + 1)));
      });
}

__attribute__((pure)) MutualCoind::streamB<unsigned int>
MutualCoind::countB(unsigned int n) {
  return streamB<unsigned int>::lazy_(
      [=]() mutable -> MutualCoind::streamB<unsigned int> {
        return streamB<unsigned int>::consb(n, countA((n + 1)));
      });
}
