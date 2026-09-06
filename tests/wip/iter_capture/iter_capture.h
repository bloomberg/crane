#ifndef INCLUDED_ITER_CAPTURE
#define INCLUDED_ITER_CAPTURE

struct IterCapture {
  static inline const uint64_t run = []() {
    return []() {
      uint64_t _acc = UINT64_C(100);
      return [&]() {
        auto _acc = UINT64_C(0);
        for (uint64_t _i = 0; _i < UINT64_C(3); _i++) {
          _acc = [=](uint64_t x) mutable {
            return (x + _acc);
          }(std::move(_acc));
        }
        return _acc;
      }();
    }();
  }();
};

#endif // INCLUDED_ITER_CAPTURE
