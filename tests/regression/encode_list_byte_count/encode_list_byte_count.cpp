#include <algorithm>
#include <any>
#include <cassert>
#include <encode_list_byte_count.h>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

std::pair<unsigned int, unsigned int> EncodeListByteCount::encode(
    const std::shared_ptr<EncodeListByteCount::instruction> &i) {
  return std::visit(
      Overloaded{
          [](const typename EncodeListByteCount::instruction::NOP _args)
              -> std::pair<unsigned int, unsigned int> {
            return std::make_pair(0, 0);
          },
          [](const typename EncodeListByteCount::instruction::LDM _args)
              -> std::pair<unsigned int, unsigned int> {
            unsigned int n = _args._a0;
            return std::make_pair(
                (((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
                    1) +
                   1) +
                  1) +
                 1),
                (std::move(n) %
                 ((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
                         1) +
                        1) +
                       1) +
                      1) +
                     1) +
                    1) +
                   1) +
                  1)));
          }},
      i->v());
}

std::shared_ptr<List<unsigned int>> EncodeListByteCount::encode_list(
    const std::shared_ptr<
        List<std::shared_ptr<EncodeListByteCount::instruction>>> &prog) {
  return std::visit(
      Overloaded{
          [](const typename List<
              std::shared_ptr<EncodeListByteCount::instruction>>::nil _args)
              -> std::shared_ptr<List<unsigned int>> {
            return List<unsigned int>::ctor::nil_();
          },
          [](const typename List<
              std::shared_ptr<EncodeListByteCount::instruction>>::cons _args)
              -> std::shared_ptr<List<unsigned int>> {
            std::shared_ptr<EncodeListByteCount::instruction> i = _args._a0;
            std::shared_ptr<
                List<std::shared_ptr<EncodeListByteCount::instruction>>>
                rest = _args._a1;
            unsigned int b1 = encode(i).first;
            unsigned int b2 = encode(i).second;
            return List<unsigned int>::ctor::cons_(
                std::move(b1), List<unsigned int>::ctor::cons_(
                                   std::move(b2), encode_list(rest)));
          }},
      prog->v());
}
