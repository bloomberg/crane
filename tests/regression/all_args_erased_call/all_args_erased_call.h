#ifndef INCLUDED_ALL_ARGS_ERASED_CALL
#define INCLUDED_ALL_ARGS_ERASED_CALL

struct AllArgsErasedCall {
  /// A definition whose only argument is a proof takes no C++ parameters, so
  /// it is emitted as a data member rather than a nullary function.  Its use
  /// sites must spell it p, not p().
  static inline const uint64_t p = []() { return UINT64_C(7); }();
  static uint64_t run(uint64_t k);
};

#endif // INCLUDED_ALL_ARGS_ERASED_CALL
