#ifndef INCLUDED_NESTED_RECORD_UPDATE_QUAL
#define INCLUDED_NESTED_RECORD_UPDATE_QUAL

struct NestedRecordUpdateQual {
  struct Shadow {
    uint64_t value;
  };

  static Shadow bump(const Shadow &x);
  static inline const Shadow t = bump(Shadow{UINT64_C(1)});
};

#endif // INCLUDED_NESTED_RECORD_UPDATE_QUAL
