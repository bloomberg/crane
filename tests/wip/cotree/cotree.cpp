#include <algorithm>
#include <any>
#include <cassert>
#include <cotree.h>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

std::shared_ptr<Cotree::colist<unsigned int>>
Cotree::nats(const unsigned int n) {
  return colist<unsigned int>::ctor::lazy_(
      [=](void) -> std::shared_ptr<Cotree::colist<unsigned int>> {
        return colist<unsigned int>::ctor::cocons_(n, nats((n + 1)));
      });
}

std::shared_ptr<Cotree::colist<unsigned int>>
Cotree::binary_children(const unsigned int n) {
  return colist<unsigned int>::ctor::lazy_(
      [=](void) -> std::shared_ptr<Cotree::colist<unsigned int>> {
        return colist<unsigned int>::ctor::cocons_(
            ((2u * n) + 1u),
            colist<unsigned int>::ctor::cocons_(
                ((2u * n) + 2u), colist<unsigned int>::ctor::conil_()));
      });
}
