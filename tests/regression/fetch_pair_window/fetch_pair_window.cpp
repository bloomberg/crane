#include <algorithm>
#include <any>
#include <cassert>
#include <fetch_pair_window.h>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

std::pair<unsigned int, unsigned int>
FetchPairWindow::fetch_pair(const std::shared_ptr<List<unsigned int>> &rom,
                            const unsigned int addr) {
  return std::visit(
      Overloaded{[](const typename List<unsigned int>::nil _args)
                     -> std::pair<unsigned int, unsigned int> {
                   return std::make_pair(0, 0);
                 },
                 [](const typename List<unsigned int>::cons _args)
                     -> std::pair<unsigned int, unsigned int> {
                   unsigned int b1 = _args._a0;
                   std::shared_ptr<List<unsigned int>> l = _args._a1;
                   return std::visit(
                       Overloaded{
                           [](const typename List<unsigned int>::nil _args)
                               -> std::pair<unsigned int, unsigned int> {
                             return std::make_pair(0, 0);
                           },
                           [&](const typename List<unsigned int>::cons _args)
                               -> std::pair<unsigned int, unsigned int> {
                             unsigned int b2 = _args._a0;
                             return std::make_pair(std::move(b1),
                                                   std::move(b2));
                           }},
                       std::move(l)->v());
                 }},
      drop<unsigned int>(addr, rom)->v());
}
