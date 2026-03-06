#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <instruction_byte_stream_encode.h>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

std::pair<unsigned int, unsigned int> InstructionByteStreamEncode::encode(
    const std::shared_ptr<InstructionByteStreamEncode::instruction> &i) {
  return std::visit(
      Overloaded{
          [](const typename InstructionByteStreamEncode::instruction::NOP _args)
              -> std::pair<unsigned int, unsigned int> {
            return std::make_pair(0, 0);
          },
          [](const typename InstructionByteStreamEncode::instruction::LDM _args)
              -> std::pair<unsigned int, unsigned int> {
            unsigned int n = _args._a0;
            return std::make_pair(
                (((((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
                      1) +
                     1) +
                    1) +
                   1) *
                  ((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
                          1) +
                         1) +
                        1) +
                       1) +
                      1) +
                     1) +
                    1) +
                   1)) +
                 (std::move(n) %
                  ((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
                          1) +
                         1) +
                        1) +
                       1) +
                      1) +
                     1) +
                    1) +
                   1))),
                0);
          }},
      i->v());
}

std::shared_ptr<List<unsigned int>> InstructionByteStreamEncode::encode_list(
    const std::shared_ptr<
        List<std::shared_ptr<InstructionByteStreamEncode::instruction>>>
        &prog) {
  return std::visit(
      Overloaded{
          [](const typename List<
              std::shared_ptr<InstructionByteStreamEncode::instruction>>::nil
                 _args) -> std::shared_ptr<List<unsigned int>> {
            return List<unsigned int>::ctor::nil_();
          },
          [](const typename List<
              std::shared_ptr<InstructionByteStreamEncode::instruction>>::cons
                 _args) -> std::shared_ptr<List<unsigned int>> {
            std::shared_ptr<InstructionByteStreamEncode::instruction> i =
                _args._a0;
            std::shared_ptr<
                List<std::shared_ptr<InstructionByteStreamEncode::instruction>>>
                rest = _args._a1;
            std::pair<unsigned int, unsigned int> p = encode(std::move(i));
            return List<unsigned int>::ctor::cons_(
                p.first, List<unsigned int>::ctor::cons_(
                             p.second, encode_list(std::move(rest))));
          }},
      prog->v());
}
