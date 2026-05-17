#ifndef INCLUDED_QUALIFIED_RECORD_SHADOW
#define INCLUDED_QUALIFIED_RECORD_SHADOW

struct QualifiedRecordShadow {
  struct Shadow {
    uint64_t value;
  };

  static Shadow bump(const Shadow &x);
  static inline const Shadow t = bump(Shadow{UINT64_C(1)});
};

#endif // INCLUDED_QUALIFIED_RECORD_SHADOW
