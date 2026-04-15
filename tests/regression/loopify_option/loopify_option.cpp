#include <loopify_option.h>

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

/// lookup_opt key l looks up key in an association list.
__attribute__((pure)) std::optional<unsigned int> LoopifyOption::lookup_opt(
    const unsigned int key,
    const std::shared_ptr<
        LoopifyOption::list<std::pair<unsigned int, unsigned int>>> &l) {
  std::optional<unsigned int> _result;
  std::shared_ptr<LoopifyOption::list<std::pair<unsigned int, unsigned int>>>
      _loop_l = l;
  bool _continue = true;
  while (_continue) {
    if (std::holds_alternative<typename LoopifyOption::list<
            std::pair<unsigned int, unsigned int>>::Nil>(_loop_l->v())) {
      _result = std::optional<unsigned int>();
      _continue = false;
    } else {
      const auto &_m = *std::get_if<typename LoopifyOption::list<
          std::pair<unsigned int, unsigned int>>::Cons>(&_loop_l->v());
      if (_m.d_a0.first == key) {
        _result = std::make_optional<unsigned int>(_m.d_a0.second);
        _continue = false;
      } else {
        _loop_l = _m.d_a1;
      }
    }
  }
  return _result;
}
