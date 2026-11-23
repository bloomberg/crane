#include "boxed_fields_match_arg_obj.h"

uint64_t BoxedFieldsMatchArgObj::count(uint64_t n) {
  return [&]() {
    auto go =
        [](const List<std::string> &l,
           List<std::optional<uint64_t>> acc)
             -> List<std::optional<uint64_t>> {
          // Loop replaces the tail recursion: each recursive call updates the
          // loop variables.
          const List<std::string> *_loop_l = &l;
          while (true) {
            if (std::holds_alternative<typename List<std::string>::Nil>(
                    _loop_l->v())) {
              return acc;
            } else {
              const auto &[_, a1] =
                  std::get<typename List<std::string>::Cons>(_loop_l->v());
              _loop_l = crane_raw(a1);
            }
          }
        };
    return go(List<std::string>::cons("a", List<std::string>::nil()),
              [&]() -> List<std::optional<uint64_t>> {
                if (n <= 0) {
                  return List<std::optional<uint64_t>>::nil();
                } else {
                  uint64_t _x = n - 1;
                  return List<std::optional<uint64_t>>::cons(
                      std::optional<uint64_t>(),
                      List<std::optional<uint64_t>>::nil());
                }
              }());
  }().length();
}
