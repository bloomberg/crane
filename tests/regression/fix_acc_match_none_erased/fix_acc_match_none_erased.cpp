#include "fix_acc_match_none_erased.h"

std::pair<std::optional<std::string>, uint64_t>
FixAccMatchNoneErased::run(const List<uint64_t> &n) {
  crane::fn<std::pair<std::optional<std::string>, uint64_t>(
      List<std::string>, std::pair<std::optional<std::string>, uint64_t>)> go =
      [](const List<std::string> &l,
         std::pair<std::optional<std::string>, uint64_t> acc) {
        if (std::holds_alternative<typename List<std::string>::Nil>(l.v())) {
          return acc;
        } else {
          return std::make_pair(std::optional<std::string>(), UINT64_C(1));
        }
      };
  return go(List<std::string>::cons("", List<std::string>::nil()),
            (std::holds_alternative<typename List<uint64_t>::Nil>(n.v())
                 ? std::make_pair(std::optional<std::string>(), UINT64_C(2))
                 : std::make_pair(std::optional<std::string>(), UINT64_C(3))));
}
