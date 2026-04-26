#include <mutual_coind.h>

#include <functional>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

std::shared_ptr<MutualCoind::streamA<unsigned int>>
MutualCoind::countA(unsigned int n) {
  return streamA<unsigned int>::lazy_(
      [=]() mutable -> std::shared_ptr<MutualCoind::streamA<unsigned int>> {
        return streamA<unsigned int>::consa(n, countB((n + 1)));
      });
}

std::shared_ptr<MutualCoind::streamB<unsigned int>>
MutualCoind::countB(unsigned int n) {
  return streamB<unsigned int>::lazy_(
      [=]() mutable -> std::shared_ptr<MutualCoind::streamB<unsigned int>> {
        return streamB<unsigned int>::consb(n, countA((n + 1)));
      });
}
