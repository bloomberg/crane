#ifndef INCLUDED_ALL_ARGS_ERASED_CALL
#define INCLUDED_ALL_ARGS_ERASED_CALL

struct AllArgsErasedCall {
  /// A definition whose only argument is a proof is emitted as a value
  /// (static inline const uint64_t p = ...), but its use site still emits a
  /// call p(): called object type 'uint64_t' is not a function.
  static inline const uint64_t p = []() { return UINT64_C(7); }();
  static uint64_t run(uint64_t k);
};

#endif // INCLUDED_ALL_ARGS_ERASED_CALL
