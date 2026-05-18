#ifndef INCLUDED_KEYWORD_CLASS_GLOBAL
#define INCLUDED_KEYWORD_CLASS_GLOBAL

struct KeywordClassGlobal {
  static uint64_t class_(uint64_t n);
  static inline const uint64_t t = class_(UINT64_C(4));
};

#endif // INCLUDED_KEYWORD_CLASS_GLOBAL
