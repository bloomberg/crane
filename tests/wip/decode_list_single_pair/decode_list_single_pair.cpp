#include <algorithm>
#include <any>
#include <cassert>
#include <decode_list_single_pair.h>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

std::shared_ptr<DecodeListSinglePair::instruction>
DecodeListSinglePair::decode(const unsigned int b1, const unsigned int b2) {
  if ((b1 == 0)) {
    return instruction::ctor::NOP_();
  } else {
    return instruction::ctor::LDM_(
        (std::move(b2) %
         ((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
               1) +
              1) +
             1) +
            1) +
           1) +
          1)));
  }
}

std::shared_ptr<List<std::shared_ptr<DecodeListSinglePair::instruction>>>
DecodeListSinglePair::decode_list(
    const std::shared_ptr<List<unsigned int>> &bytes) {
  return std::visit(
      Overloaded{
          [](const typename List<unsigned int>::nil _args)
              -> std::shared_ptr<
                  List<std::shared_ptr<DecodeListSinglePair::instruction>>> {
            return List<std::shared_ptr<DecodeListSinglePair::instruction>>::
                ctor::nil_();
          },
          [](const typename List<unsigned int>::cons _args)
              -> std::shared_ptr<
                  List<std::shared_ptr<DecodeListSinglePair::instruction>>> {
            unsigned int b1 = _args._a0;
            std::shared_ptr<List<unsigned int>> l = _args._a1;
            return [&](void) {
              if (std::move(l).use_count() == 1 &&
                  std::move(l)->v().index() == 0) {
                auto &_rf = std::get<0>(std::move(l)->v_mut());
                return std::move(l);
              } else {
                return std::visit(
                    Overloaded{
                        [](const typename List<unsigned int>::nil _args)
                            -> std::shared_ptr<List<std::shared_ptr<
                                DecodeListSinglePair::instruction>>> {
                          return List<std::shared_ptr<
                              DecodeListSinglePair::instruction>>::ctor::nil_();
                        },
                        [&](const typename List<unsigned int>::cons _args)
                            -> std::shared_ptr<List<std::shared_ptr<
                                DecodeListSinglePair::instruction>>> {
                          unsigned int b2 = _args._a0;
                          std::shared_ptr<List<unsigned int>> rest = _args._a1;
                          return List<std::shared_ptr<
                              DecodeListSinglePair::instruction>>::ctor::
                              cons_(decode(std::move(b1), std::move(b2)),
                                    decode_list(std::move(rest)));
                        }},
                    std::move(l)->v());
              }
            }();
          }},
      bytes->v());
}
