#include "hkt_class_param.h"

uint64_t HktClassParam::run(uint64_t k) {
  return (toList<HktClassParam::ListContainer, uint64_t>(
              build<HktClassParam::ListContainer>(List<uint64_t>::cons(
                  UINT64_C(1),
                  List<uint64_t>::cons(
                      UINT64_C(2), List<uint64_t>::cons(
                                       UINT64_C(3), List<uint64_t>::nil())))))
              .length() +
          k);
}
