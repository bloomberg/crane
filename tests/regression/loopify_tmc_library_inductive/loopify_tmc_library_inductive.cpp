#include "loopify_tmc_library_inductive.h"

LoopifyTmcLibraryInductive::digit
LoopifyTmcLibraryInductive::digit_of_nat(uint64_t n) {
  return Fin::of_nat_lt(n, UINT64_C(10));
}

uint64_t LoopifyTmcLibraryInductive::digit_to_nat(const T &d) {
  return d.to_nat(UINT64_C(10));
}

T Fin::of_nat_lt(uint64_t p, uint64_t n) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
  std::optional<T> _root{};
  std::shared_ptr<T> *_write = nullptr;
  while (true) {
    if (n <= 0) {
      throw std::logic_error("absurd case");
    } else {
      uint64_t n_ = n - 1;
      if (p <= 0) {
        auto _value = T::f1(n_);
        (_write ? *(*_write = std::make_shared<T>(std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        uint64_t p_ = p - 1;
        auto _cell = typename T::FS(n_, nullptr);
        T &_node = (_write ? *(*_write = std::make_shared<T>(std::move(_cell)))
                           : _root.emplace(std::move(_cell)));
        _write = &std::get<typename T::FS>(_node.v_mut()).a1;
        n = n_;
        p = p_;
        continue;
      }
    }
  }
  return std::move(*_root);
}
