#include <loopify_option.h>

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

/// lookup_opt key l looks up key in an association list.
__attribute__((pure)) std::optional<unsigned int> LoopifyOption::lookup_opt(
    const unsigned int &key,
    const LoopifyOption::list<std::pair<unsigned int, unsigned int>> &l) {
  std::optional<unsigned int> _result;
  LoopifyOption::list<std::pair<unsigned int, unsigned int>> _loop_l = l;
  while (true) {
    if (std::holds_alternative<typename LoopifyOption::list<
            std::pair<unsigned int, unsigned int>>::Nil>(_loop_l.v())) {
      _result = std::optional<unsigned int>();
      break;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename LoopifyOption::list<
          std::pair<unsigned int, unsigned int>>::Cons>(_loop_l.v());
      if (d_a0.first == key) {
        _result = std::make_optional<unsigned int>(d_a0.second);
        break;
      } else {
        _loop_l = *(d_a1);
      }
    }
  }
  return _result;
}
