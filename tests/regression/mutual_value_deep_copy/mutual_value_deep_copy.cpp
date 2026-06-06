#include "mutual_value_deep_copy.h"

bool MutualValueDeepCopy::reaches_end_a(const MutualValueDeepCopy::a &x) {
  const MutualValueDeepCopy::a *_loop_x = &x;
  while (true) {
    if (std::holds_alternative<typename MutualValueDeepCopy::a::AEnd>(
            _loop_x->v())) {
      return true;
    } else {
      const auto &[a0, a1] =
          std::get<typename MutualValueDeepCopy::a::ANode>(_loop_x->v());
      const MutualValueDeepCopy::b &_inl_y = *a1;
      const auto &[_inl_a0] =
          std::get<typename MutualValueDeepCopy::b::BNode>(_inl_y.v());
      _loop_x = _inl_a0.get();
    }
  }
}

bool MutualValueDeepCopy::reaches_end_b(const MutualValueDeepCopy::b &y) {
  const MutualValueDeepCopy::b *_loop_y = &y;
  while (true) {
    const auto &[a0] =
        std::get<typename MutualValueDeepCopy::b::BNode>(_loop_y->v());
    const MutualValueDeepCopy::a &_inl_x = *a0;
    if (std::holds_alternative<typename MutualValueDeepCopy::a::AEnd>(
            _inl_x.v())) {
      return true;
    } else {
      const auto &[_inl_a0, _inl_a1] =
          std::get<typename MutualValueDeepCopy::a::ANode>(_inl_x.v());
      _loop_y = _inl_a1.get();
    }
  }
}

std::pair<MutualValueDeepCopy::a, MutualValueDeepCopy::a>
MutualValueDeepCopy::dup_a(MutualValueDeepCopy::a x) {
  return std::make_pair(x, x);
}

bool MutualValueDeepCopy::copied_reaches_end(const MutualValueDeepCopy::a &x) {
  auto _cs = dup_a(x);
  MutualValueDeepCopy::a x1 = std::move(_cs.first);
  MutualValueDeepCopy::a x2 = std::move(_cs.second);
  return (reaches_end_a(std::move(x1)) && reaches_end_a(std::move(x2)));
}
