#include <cotree.h>

#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

std::shared_ptr<Cotree::colist<unsigned int>>
Cotree::nats(const unsigned int n) {
  return colist<unsigned int>::lazy_(
      [=](void) mutable -> std::shared_ptr<Cotree::colist<unsigned int>> {
        return colist<unsigned int>::cocons(n, nats((n + 1)));
      });
}

std::shared_ptr<Cotree::colist<unsigned int>>
Cotree::binary_children(const unsigned int n) {
  return colist<unsigned int>::lazy_(
      [=](void) mutable -> std::shared_ptr<Cotree::colist<unsigned int>> {
        return colist<unsigned int>::cocons(
            ((2u * n) + 1u),
            colist<unsigned int>::cocons(((2u * n) + 2u),
                                         colist<unsigned int>::conil()));
      });
}
