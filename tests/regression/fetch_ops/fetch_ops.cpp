#include <fetch_ops.h>

#include <memory>
#include <optional>
#include <type_traits>
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
      Overloaded{[](const typename List<unsigned int>::Nil &)
                     -> std::pair<unsigned int, unsigned int> {
                   return std::make_pair(0u, 0u);
                 },
                 [](const typename List<unsigned int>::Cons &_args)
                     -> std::pair<unsigned int, unsigned int> {
                   return std::visit(
                       Overloaded{
                           [](const typename List<unsigned int>::Nil &)
                               -> std::pair<unsigned int, unsigned int> {
                             return std::make_pair(0u, 0u);
                           },
                           [&](const typename List<unsigned int>::Cons &_args0)
                               -> std::pair<unsigned int, unsigned int> {
                             return std::make_pair(_args.d_a0, _args0.d_a0);
                           }},
                       _args.d_a1->v());
                 }},
      drop<unsigned int>(addr, rom_data)->v());
}

__attribute__((pure)) std::optional<std::pair<unsigned int, unsigned int>>
FetchOps::fetch_window(const std::shared_ptr<List<unsigned int>> &rom_data,
                       const unsigned int addr) {
  return std::visit(
      Overloaded{
          [](const typename List<unsigned int>::Nil &)
              -> std::optional<std::pair<unsigned int, unsigned int>> {
            return std::optional<std::pair<unsigned int, unsigned int>>();
          },
          [&](const typename List<unsigned int>::Cons &_args)
              -> std::optional<std::pair<unsigned int, unsigned int>> {
            return std::visit(
                Overloaded{[](const typename List<unsigned int>::Nil &)
                               -> std::optional<
                                   std::pair<unsigned int, unsigned int>> {
                             return std::optional<
                                 std::pair<unsigned int, unsigned int>>();
                           },
                           [&](const typename List<unsigned int>::Cons &)
                               -> std::optional<
                                   std::pair<unsigned int, unsigned int>> {
                             return std::make_optional<
                                 std::pair<unsigned int, unsigned int>>(
                                 std::make_pair(_args.d_a0, (addr + 2u)));
                           }},
                _args.d_a1->v());
          }},
      drop<unsigned int>(addr, rom_data)->v());
}
