#include <cotree.h>

Cotree::colist<unsigned int> Cotree::nats(unsigned int n) {
  return colist<unsigned int>::lazy_(
      [=]() mutable -> Cotree::colist<unsigned int> {
        return colist<unsigned int>::cocons(n, nats((n + 1)));
      });
}

Cotree::colist<unsigned int> Cotree::binary_children(const unsigned int &n) {
  return colist<unsigned int>::lazy_(
      [=]() mutable -> Cotree::colist<unsigned int> {
        return colist<unsigned int>::cocons(
            ((2u * n) + 1u),
            colist<unsigned int>::cocons(((2u * n) + 2u),
                                         colist<unsigned int>::conil()));
      });
}
