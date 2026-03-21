#include <loopify_option.h>

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
    std::visit(
        Overloaded{[&](const typename LoopifyOption::list<
                       std::pair<unsigned int, unsigned int>>::Nil _args) {
                     _result = std::nullopt;
                     _continue = false;
                   },
                   [&](const typename LoopifyOption::list<
                       std::pair<unsigned int, unsigned int>>::Cons _args) {
                     if (_args.d_a0.first == key) {
                       _result =
                           std::make_optional<unsigned int>(_args.d_a0.second);
                       _continue = false;
                     } else {
                       _loop_l = _args.d_a1;
                     }
                   }},
        _loop_l->v());
  }
  return _result;
}
