#include <mutual_value_deep_copy.h>

bool MutualValueDeepCopy::reaches_end_a(const MutualValueDeepCopy::a &x) {
  if (std::holds_alternative<typename MutualValueDeepCopy::a::AEnd>(x.v())) {
    return true;
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename MutualValueDeepCopy::a::ANode>(x.v());
    return reaches_end_b(*(d_a1));
  }
}

bool MutualValueDeepCopy::reaches_end_b(const MutualValueDeepCopy::b &y) {
  const auto &[d_a0] = std::get<typename MutualValueDeepCopy::b::BNode>(y.v());
  return reaches_end_a(*(d_a0));
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
