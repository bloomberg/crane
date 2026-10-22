#include "loopify_shadow_update_reads_binding.h"

/// A tail loop whose new arguments read a field of the list it walks.
///
/// One call passes a fresh list, so fs is kept by value in _loop_fs,
/// and the match binds f and rest by reference into that value.  The
/// updates were staged in a temporary only where one names another's
/// variable, and f v names f, not _loop_fs: _loop_fs was assigned
/// rest first, and f then read the same storage, now the next cell's
/// function.
uint64_t LoopifyShadowUpdateReadsBinding::apply_n(
    uint64_t n, uint64_t v, const List<crane::fn<uint64_t(uint64_t)>> &fs) {
  List<crane::fn<uint64_t(uint64_t)>> _loop_fs = fs;
  uint64_t _loop_v = v;
  uint64_t _loop_n = n;
  while (true) {
    if (_loop_n <= 0) {
      return _loop_v;
    } else {
      uint64_t m = _loop_n - 1;
      if (std::holds_alternative<
              typename List<crane::fn<uint64_t(uint64_t)>>::Nil>(
              _loop_fs.v())) {
        _loop_fs = List<crane::fn<uint64_t(uint64_t)>>::nil();
        _loop_n = m;
      } else {
        const auto &[a0, a1] =
            std::get<typename List<crane::fn<uint64_t(uint64_t)>>::Cons>(
                _loop_fs.v());
        List<crane::fn<uint64_t(uint64_t)>> _next_fs =
            List<crane::fn<uint64_t(uint64_t)>>(*a1);
        _loop_v = a0(_loop_v);
        _loop_n = m;
        _loop_fs = std::move(_next_fs);
      }
    }
  }
}
