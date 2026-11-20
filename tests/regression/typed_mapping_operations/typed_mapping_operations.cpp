#include "typed_mapping_operations.h"

uint64_t TypedMappingOperations::counted(uint64_t n) {
  return static_cast<std::uint64_t>(
      (static_cast<std::int64_t>(n) + static_cast<std::int64_t>(UINT64_C(2))));
}

std::int64_t TypedMappingOperations::doubled(std::int64_t c) {
  auto _once1 = ops_support::log_counter(c);
  return (_once1 + _once1);
}

uint64_t TypedMappingOperations::ordered(uint64_t x, uint64_t y) {
  auto _once1 = ops_support::tick(x);
  auto _once2 = ops_support::tick(y);
  return ops_support::combine(std::move(_once2), _once1, _once1);
}

uint64_t TypedMappingOperations::skipped(uint64_t x, uint64_t y) {
  ops_support::tick(x);
  auto _once1 = ops_support::tick(y);
  return (std::move(_once1) + 1);
}

uint64_t TypedMappingOperations::skipped_pure(uint64_t, uint64_t y) {
  return (ops_support::tick(y) + 1);
}

uint64_t TypedMappingOperations::size_of(const ops_support::buffer &x0_) {
  return static_cast<std::uint64_t>(x0_.items.size());
}

ops_support::buffer TypedMappingOperations::push_one(ops_support::buffer b) {
  return ops_support::push(std::move(b), UINT64_C(1));
}

std::pair<ops_support::buffer, uint64_t>
TypedMappingOperations::push_keep(ops_support::buffer b) {
  ops_support::buffer c = ops_support::push(b, UINT64_C(1));
  return std::make_pair(std::move(c),
                        static_cast<std::uint64_t>(b.items.size()));
}

ops_support::buffer TypedMappingOperations::checked_one(ops_support::buffer b) {
  return ops_support::push(std::move(b), UINT64_C(1));
}

uint64_t
TypedMappingOperations::poke_twice(const std::shared_ptr<std::int64_t> &c) {
  return static_cast<std::uint64_t>(
      *ops_support::poke(ops_support::poke(c, UINT64_C(1)), UINT64_C(2)));
}

uint64_t TypedMappingOperations::fresh_cell(uint64_t n) {
  return static_cast<std::uint64_t>(
      *std::make_shared<std::int64_t>(static_cast<std::int64_t>(n)));
}

bool TypedMappingOperations::boxed(uint64_t n, bool b) {
  return bool(std::vector<bool>(static_cast<std::size_t>(n), b)[UINT64_C(0)]);
}
