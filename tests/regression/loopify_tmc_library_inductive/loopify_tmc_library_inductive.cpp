#include "loopify_tmc_library_inductive.h"

LoopifyTmcLibraryInductive::digit
LoopifyTmcLibraryInductive::digit_of_nat(uint64_t n) {
  return Fin::of_nat_lt(n, UINT64_C(10));
}

uint64_t LoopifyTmcLibraryInductive::digit_to_nat(const T &d) {
  const auto &_sv = d.to_nat(UINT64_C(10));
  const auto &[x] = _sv;
  return x;
}

T Fin::of_nat_lt(uint64_t p, uint64_t n) {
  std::optional<T> _root{};
  std::shared_ptr<T> *_write = nullptr;
  uint64_t _loop_n = n;
  uint64_t _loop_p = p;
  while (true) {
    if (_loop_n <= 0) {
      throw std::logic_error("absurd case");
    } else {
      uint64_t n_ = _loop_n - 1;
      if (_loop_p <= 0) {
        auto _value = T::f1(n_);
        (_write ? *(*_write = std::make_shared<T>(std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        uint64_t p_ = _loop_p - 1;
        auto _cell = typename T::FS(n_, nullptr);
        T &_node = (_write ? *(*_write = std::make_shared<T>(std::move(_cell)))
                           : _root.emplace(std::move(_cell)));
        _write = &std::get<typename T::FS>(_node.v_mut()).a1;
        _loop_n = n_;
        _loop_p = p_;
        continue;
      }
    }
  }
  return std::move(*_root);
}
