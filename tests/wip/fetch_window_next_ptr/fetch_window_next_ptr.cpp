#include <algorithm>
#include <any>
#include <cassert>
#include <fetch_window_next_ptr.h>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

std::shared_ptr<List<unsigned int>>
FetchWindowNextPtr::drop(const unsigned int n,
                         std::shared_ptr<List<unsigned int>> l) {
  if (n <= 0) {
    return std::move(l);
  } else {
    unsigned int n_ = n - 1;
    return std::visit(
        Overloaded{[](const typename List<unsigned int>::nil _args)
                       -> std::shared_ptr<List<unsigned int>> {
                     return List<unsigned int>::ctor::nil_();
                   },
                   [&](const typename List<unsigned int>::cons _args)
                       -> std::shared_ptr<List<unsigned int>> {
                     std::shared_ptr<List<unsigned int>> l_ = _args._a1;
                     return drop(std::move(n_), std::move(l_));
                   }},
        l->v());
  }
}

std::optional<std::pair<unsigned int, unsigned int>>
FetchWindowNextPtr::fetch_window(const std::shared_ptr<List<unsigned int>> &rom,
                                 const unsigned int addr) {
  return std::visit(
      Overloaded{
          [](const typename List<unsigned int>::nil _args)
              -> std::optional<std::pair<unsigned int, unsigned int>> {
            return std::nullopt;
          },
          [&](const typename List<unsigned int>::cons _args)
              -> std::optional<std::pair<unsigned int, unsigned int>> {
            unsigned int b1 = _args._a0;
            std::shared_ptr<List<unsigned int>> l = _args._a1;
            return std::visit(
                Overloaded{
                    [](const typename List<unsigned int>::nil _args)
                        -> std::optional<
                            std::pair<unsigned int, unsigned int>> {
                      return std::nullopt;
                    },
                    [&](const typename List<unsigned int>::cons _args)
                        -> std::optional<
                            std::pair<unsigned int, unsigned int>> {
                      return std::make_optional<
                          std::pair<unsigned int, unsigned int>>(std::make_pair(
                          std::move(b1), (std::move(addr) + ((0 + 1) + 1))));
                    }},
                std::move(l)->v());
          }},
      drop(addr, rom)->v());
}
