#include <decode_list.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

std::shared_ptr<DecodeList::instruction>
DecodeList::decode(const unsigned int b1, const unsigned int b2) {
  if (b1 == 0u) {
    return instruction::nop();
  } else {
    return instruction::ldm((16u ? b2 % 16u : b2));
  }
}

std::shared_ptr<List<std::shared_ptr<DecodeList::instruction>>>
DecodeList::decode_list(const std::shared_ptr<List<unsigned int>> &bytes) {
  return std::visit(
      Overloaded{
          [](const typename List<unsigned int>::Nil)
              -> std::shared_ptr<
                  List<std::shared_ptr<DecodeList::instruction>>> {
            return List<std::shared_ptr<DecodeList::instruction>>::nil();
          },
          [](const typename List<unsigned int>::Cons _args)
              -> std::shared_ptr<
                  List<std::shared_ptr<DecodeList::instruction>>> {
            return std::visit(
                Overloaded{
                    [](const typename List<unsigned int>::Nil)
                        -> std::shared_ptr<
                            List<std::shared_ptr<DecodeList::instruction>>> {
                      return List<
                          std::shared_ptr<DecodeList::instruction>>::nil();
                    },
                    [&](const typename List<unsigned int>::Cons _args0)
                        -> std::shared_ptr<
                            List<std::shared_ptr<DecodeList::instruction>>> {
                      return List<std::shared_ptr<DecodeList::instruction>>::
                          cons(decode(_args.d_a0, _args0.d_a0),
                               decode_list(_args0.d_a1));
                    }},
                _args.d_a1->v());
          }},
      bytes->v());
}
