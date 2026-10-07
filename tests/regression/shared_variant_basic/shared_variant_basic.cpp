#include "shared_variant_basic.h"

SharedVariantBasic::tree
SharedVariantBasic::insert(uint64_t k, uint64_t v,
                           const SharedVariantBasic::tree &t) {
  if (crane::holds_alternative<typename SharedVariantBasic::tree::Leaf>(
          t.v())) {
    return tree::node(tree::leaf(), k, v, tree::leaf());
  } else {
    const auto &[a0, a1, a2, a3] =
        crane::get<typename SharedVariantBasic::tree::Node>(t.v());
    if (k < a1) {
      return tree::node(insert(k, v, *a0), a1, a2, *a3);
    } else {
      if (a1 < k) {
        return tree::node(*a0, a1, a2, insert(k, v, *a3));
      } else {
        return tree::node(*a0, k, v, *a3);
      }
    }
  }
}

std::optional<uint64_t>
SharedVariantBasic::find(uint64_t k, const SharedVariantBasic::tree &t) {
  if (crane::holds_alternative<typename SharedVariantBasic::tree::Leaf>(
          t.v())) {
    return std::optional<uint64_t>();
  } else {
    const auto &[a0, a1, a2, a3] =
        crane::get<typename SharedVariantBasic::tree::Node>(t.v());
    if (k < a1) {
      return find(k, *a0);
    } else {
      if (a1 < k) {
        return find(k, *a3);
      } else {
        return std::make_optional<uint64_t>(a2);
      }
    }
  }
}

uint64_t SharedVariantBasic::size(const SharedVariantBasic::tree &t) {
  if (crane::holds_alternative<typename SharedVariantBasic::tree::Leaf>(
          t.v())) {
    return UINT64_C(0);
  } else {
    const auto &[a0, a1, a2, a3] =
        crane::get<typename SharedVariantBasic::tree::Node>(t.v());
    return ((UINT64_C(1) + size(*a0)) + size(*a3));
  }
}

List<uint64_t> SharedVariantBasic::bump(const List<uint64_t> &l) {
  return l.template map<uint64_t>([](uint64_t x) { return (x + 1); });
}

uint64_t SharedVariantBasic::long_result(uint64_t n) {
  return ListDef::seq(UINT64_C(0), n).length();
}

List<uint64_t> ListDef::seq(uint64_t start, uint64_t len) {
  std::optional<List<uint64_t>> _root{};
  crane::shared_box<List<uint64_t>> *_write = nullptr;
  uint64_t _loop_len = len;
  uint64_t _loop_start = start;
  while (true) {
    if (_loop_len <= 0) {
      auto _value = List<uint64_t>::nil();
      (_write ? *(*_write = crane::shared_box<List<uint64_t>>::make(
                      std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      uint64_t len0 = _loop_len - 1;
      auto _cell = typename List<uint64_t>::Cons(_loop_start, nullptr);
      List<uint64_t> &_node =
          (_write ? *(*_write = crane::shared_box<List<uint64_t>>::make(
                          std::move(_cell)))
                  : _root.emplace(std::move(_cell)));
      _write = &crane::get<typename List<uint64_t>::Cons>(_node.v_mut()).l;
      _loop_len = len0;
      _loop_start = (_loop_start + 1);
      continue;
    }
  }
  return std::move(*_root);
}
