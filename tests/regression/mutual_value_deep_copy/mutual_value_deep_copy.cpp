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
      auto &&_sv0 = *a1;
      const auto &[a00] =
          std::get<typename MutualValueDeepCopy::b::BNode>(_sv0.v());
      _loop_x = crane_raw(a00);
    }
  }
}

bool MutualValueDeepCopy::reaches_end_b(const MutualValueDeepCopy::b &y) {
  const MutualValueDeepCopy::b *_loop_y = &y;
  while (true) {
    const auto &[a0] =
        std::get<typename MutualValueDeepCopy::b::BNode>(_loop_y->v());
    auto &&_sv0 = *a0;
    if (std::holds_alternative<typename MutualValueDeepCopy::a::AEnd>(
            _sv0.v())) {
      return true;
    } else {
      const auto &[a00, a10] =
          std::get<typename MutualValueDeepCopy::a::ANode>(_sv0.v());
      _loop_y = crane_raw(a10);
    }
  }
}

std::pair<MutualValueDeepCopy::a, MutualValueDeepCopy::a>
MutualValueDeepCopy::dup_a(const MutualValueDeepCopy::a &x) {
  return std::make_pair(x, x);
}

bool MutualValueDeepCopy::copied_reaches_end(const MutualValueDeepCopy::a &x) {
  auto [x1, x2] = dup_a(x);
  return (reaches_end_a(std::move(x1)) && reaches_end_a(std::move(x2)));
}
