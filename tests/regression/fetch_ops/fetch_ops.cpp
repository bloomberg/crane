#include <fetch_ops.h>

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

__attribute__((pure)) unsigned int
FetchOps::fetch_byte(const std::shared_ptr<FetchOps::state> &s,
                     const unsigned int addr) {
  return s->rom->nth(addr, 0u);
}

__attribute__((pure)) unsigned int
FetchOps::fetch_byte_direct(const std::shared_ptr<List<unsigned int>> &rom_data,
                            const unsigned int addr) {
  return rom_data->nth(addr, 0u);
}

__attribute__((pure)) std::pair<unsigned int, unsigned int>
FetchOps::fetch_pair(const std::shared_ptr<List<unsigned int>> &rom_data,
                     const unsigned int addr) {
  return std::visit(
      Overloaded{[](const typename List<unsigned int>::Nil _args)
                     -> std::pair<unsigned int, unsigned int> {
                   return std::make_pair(0u, 0u);
                 },
                 [](const typename List<unsigned int>::Cons _args)
                     -> std::pair<unsigned int, unsigned int> {
                   unsigned int b1 = _args.d_a0;
                   std::shared_ptr<List<unsigned int>> l = _args.d_a1;
                   return std::visit(
                       Overloaded{
                           [](const typename List<unsigned int>::Nil _args)
                               -> std::pair<unsigned int, unsigned int> {
                             return std::make_pair(0u, 0u);
                           },
                           [&](const typename List<unsigned int>::Cons _args)
                               -> std::pair<unsigned int, unsigned int> {
                             unsigned int b2 = _args.d_a0;
                             return std::make_pair(std::move(b1),
                                                   std::move(b2));
                           }},
                       std::move(l)->v());
                 }},
      drop<unsigned int>(addr, rom_data)->v());
}

__attribute__((pure)) std::optional<std::pair<unsigned int, unsigned int>>
FetchOps::fetch_window(const std::shared_ptr<List<unsigned int>> &rom_data,
                       const unsigned int addr) {
  return std::visit(
      Overloaded{[](const typename List<unsigned int>::Nil _args)
                     -> std::optional<std::pair<unsigned int, unsigned int>> {
                   return std::nullopt;
                 },
                 [&](const typename List<unsigned int>::Cons _args)
                     -> std::optional<std::pair<unsigned int, unsigned int>> {
                   unsigned int b1 = _args.d_a0;
                   std::shared_ptr<List<unsigned int>> l = _args.d_a1;
                   return std::visit(
                       Overloaded{
                           [](const typename List<unsigned int>::Nil _args)
                               -> std::optional<
                                   std::pair<unsigned int, unsigned int>> {
                             return std::nullopt;
                           },
                           [&](const typename List<unsigned int>::Cons _args)
                               -> std::optional<
                                   std::pair<unsigned int, unsigned int>> {
                             return std::make_optional<
                                 std::pair<unsigned int, unsigned int>>(
                                 std::make_pair(std::move(b1),
                                                (std::move(addr) + 2u)));
                           }},
                       std::move(l)->v());
                 }},
      drop<unsigned int>(addr, rom_data)->v());
}
