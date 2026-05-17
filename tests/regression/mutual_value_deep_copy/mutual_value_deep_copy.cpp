#include "mutual_value_deep_copy.h"

bool MutualValueDeepCopy::reaches_end_a(const MutualValueDeepCopy::a &x) {
  bool _result;
  const MutualValueDeepCopy::a *_loop_x = &x;
  while (true) {
    if (std::holds_alternative<typename MutualValueDeepCopy::a::AEnd>(
            _loop_x->v())) {
      _result = true;
      break;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename MutualValueDeepCopy::a::ANode>(_loop_x->v());
      const MutualValueDeepCopy::b &_inl_y = *d_a1;
      const auto &[_inl_d_a0] =
          std::get<typename MutualValueDeepCopy::b::BNode>(_inl_y.v());
      _loop_x = _inl_d_a0.get();
    }
  }
  return _result;
}

bool MutualValueDeepCopy::reaches_end_b(const MutualValueDeepCopy::b &y) {
  bool _result;
  const MutualValueDeepCopy::b *_loop_y = &y;
  while (true) {
    const auto &[d_a0] =
        std::get<typename MutualValueDeepCopy::b::BNode>(_loop_y->v());
    const MutualValueDeepCopy::a &_inl_x = *d_a0;
    if (std::holds_alternative<typename MutualValueDeepCopy::a::AEnd>(
            _inl_x.v())) {
      _result = true;
      break;
    } else {
      const auto &[_inl_d_a0, _inl_d_a1] =
          std::get<typename MutualValueDeepCopy::a::ANode>(_inl_x.v());
      _loop_y = _inl_d_a1.get();
    }
  }
  return _result;
}

std::pair<MutualValueDeepCopy::a, MutualValueDeepCopy::a>
MutualValueDeepCopy::dup_a(MutualValueDeepCopy::a x) {
  return std::make_pair(x, x);
}

bool MutualValueDeepCopy::copied_reaches_end(const MutualValueDeepCopy::a &x) {
  auto _cs = dup_a(x);
  const MutualValueDeepCopy::a &x1 = _cs.first;
  const MutualValueDeepCopy::a &x2 = _cs.second;
  return (reaches_end_a(x1) && reaches_end_a(x2));
}
