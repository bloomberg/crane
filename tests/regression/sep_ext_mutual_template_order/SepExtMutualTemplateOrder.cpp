#include "SepExtMutualTemplateOrder.h"

#include "Tr.h"
#include "Ty.h"

namespace SepExtMutualTemplateOrder {

Ty::Tree<bool> use_it(const Ty::Tree<bool> &t) {
  return Tr::template tmap<bool, bool>([](bool _x0) -> bool { return !(_x0); },
                                       t);
}

} // namespace SepExtMutualTemplateOrder
