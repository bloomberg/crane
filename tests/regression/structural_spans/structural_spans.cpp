#include "structural_spans.h"

uint64_t StructuralSpans::total(std::span<const uint64_t> x0_) {
  return std::accumulate(x0_.begin(), x0_.end(), uint64_t{});
}

void StructuralSpans::bump(std::span<uint64_t> b, uint64_t i) {
  uint64_t x = std::span<const uint64_t>{b}[i];
  b[i] = (x + 1);
  return;
}

void StructuralSpans::grow(std::vector<uint64_t> &b, uint64_t n) {
  std::span<uint64_t>{b}[UINT64_C(0)] = UINT64_C(7);
  b.resize(n, UINT64_C(1));
  return;
}

uint64_t StructuralSpans::window_total(std::span<const uint64_t> b) {
  auto _once1 = b.subspan(UINT64_C(1), UINT64_C(2));
  return std::accumulate(_once1.begin(), _once1.end(), uint64_t{});
}

std::vector<uint64_t> StructuralSpans::window(std::span<const uint64_t> b) {
  auto _view1 = b.subspan(UINT64_C(1), UINT64_C(2));
  return std::vector<uint64_t>(_view1.begin(), _view1.end());
}

/// A subspan of a temporary buffer, bound ahead of buf_total (which
/// places its argument twice): the temporary is bound ahead too, so
/// that it outlives the view.
uint64_t StructuralSpans::fresh_window_total(uint64_t n) {
  auto _view1 = std::vector<uint64_t>(n, UINT64_C(3));
  auto _once1 =
      (std::span<const uint64_t>{_view1}).subspan(UINT64_C(1), UINT64_C(2));
  return std::accumulate(_once1.begin(), _once1.end(), uint64_t{});
}

void StructuralSpans::self_append(std::vector<uint64_t> &b) {
  auto _view1 = std::span<const uint64_t>{b};
  auto _view2 = std::vector<uint64_t>(_view1.begin(), _view1.end());
  b.insert(b.end(), (std::span<const uint64_t>{_view2}).begin(),
           (std::span<const uint64_t>{_view2}).end());
  return;
}

std::pair<std::pair<std::pair<List<uint64_t>, uint64_t>, uint64_t>,
          List<uint64_t>> StructuralSpans::scenario(uint64_t n) {
  std::vector<uint64_t> b = std::vector<uint64_t>(UINT64_C(3), UINT64_C(1));
  bump(std::span<uint64_t>{b}, UINT64_C(1));
  grow(b, n);
  self_append(b);
  return std::make_pair(
      std::make_pair(std::make_pair(
          crane::st::elems<List<uint64_t>>(std::span<const uint64_t>{b}),
          total(std::span<const uint64_t>{b})),
                     window_total(std::span<const uint64_t>{b})),
      crane::st::elems<List<uint64_t>>(
          std::span<const uint64_t>{window(std::span<const uint64_t>{b})}));
}
