#ifndef INCLUDED_ALL_ARGS_ERASED_CALL
#define INCLUDED_ALL_ARGS_ERASED_CALL

struct AllArgsErasedCall {
  static inline const uint64_t p = []() { return UINT64_C(7); }();
  static uint64_t run(uint64_t k);
};

#endif // INCLUDED_ALL_ARGS_ERASED_CALL
