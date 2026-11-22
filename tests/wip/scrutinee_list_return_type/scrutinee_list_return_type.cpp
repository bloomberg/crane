#include "scrutinee_list_return_type.h"

List<std::pair<std::string, uint64_t>> ScrutineeListReturnType::pairs(bool) {
  auto l = List<std::pair<std::string, uint64_t>>::cons(
      Sum<std::string, crane::obj>::inl("b"),
      List<std::pair<std::string, uint64_t>>::nil());
  if (std::holds_alternative<typename List<Sum<std::string, crane::obj>>::Nil>(
          l.v_mut())) {
    return List<std::pair<std::string, uint64_t>>::cons(
        std::make_pair(std::string("x"), UINT64_C(1)),
        List<std::pair<std::string, uint64_t>>::nil());
  } else {
    return List<std::pair<std::string, uint64_t>>::nil();
  }
}
