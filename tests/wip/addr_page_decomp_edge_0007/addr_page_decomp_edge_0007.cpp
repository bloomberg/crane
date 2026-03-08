#include <addr_page_decomp_edge_0007.h>
#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

std::shared_ptr<AddrPageDecompEdge0007::instruction>
AddrPageDecompEdge0007::decode(const unsigned int b1, const unsigned int b2) {
  if ((b1 == 0u)) {
    return instruction::ctor::NOP_();
  } else {
    return instruction::ctor::LDM_((std::move(b2) % 16u));
  }
}

std::shared_ptr<List<std::shared_ptr<AddrPageDecompEdge0007::instruction>>>
AddrPageDecompEdge0007::decode_list(
    const std::shared_ptr<List<unsigned int>> &bytes) {
  return std::visit(
      Overloaded{
          [](const typename List<unsigned int>::nil _args)
              -> std::shared_ptr<
                  List<std::shared_ptr<AddrPageDecompEdge0007::instruction>>> {
            return List<std::shared_ptr<AddrPageDecompEdge0007::instruction>>::
                ctor::nil_();
          },
          [](const typename List<unsigned int>::cons _args)
              -> std::shared_ptr<
                  List<std::shared_ptr<AddrPageDecompEdge0007::instruction>>> {
            unsigned int b1 = _args._a0;
            std::shared_ptr<List<unsigned int>> l = _args._a1;
            return [&](void) {
              if (((std::move(l).use_count() == 1) &&
                   (std::move(l)->v().index() == 0))) {
                auto &_rf = std::get<0>(std::move(l)->v_mut());
                return std::move(l);
              } else {
                return std::visit(
                    Overloaded{
                        [](const typename List<unsigned int>::nil _args)
                            -> std::shared_ptr<List<std::shared_ptr<
                                AddrPageDecompEdge0007::instruction>>> {
                          return List<std::shared_ptr<
                              AddrPageDecompEdge0007::instruction>>::ctor::
                              nil_();
                        },
                        [&](const typename List<unsigned int>::cons _args)
                            -> std::shared_ptr<List<std::shared_ptr<
                                AddrPageDecompEdge0007::instruction>>> {
                          unsigned int b2 = _args._a0;
                          std::shared_ptr<List<unsigned int>> rest = _args._a1;
                          return List<std::shared_ptr<
                              AddrPageDecompEdge0007::instruction>>::ctor::
                              cons_(decode(std::move(b1), std::move(b2)),
                                    decode_list(std::move(rest)));
                        }},
                    std::move(l)->v());
              }
            }();
          }},
      bytes->v());
}
