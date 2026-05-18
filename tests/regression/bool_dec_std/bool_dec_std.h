#ifndef INCLUDED_BOOL_DEC_STD
#define INCLUDED_BOOL_DEC_STD

struct Bool {
  static bool bool_dec(bool b1, bool b2);
};

struct BoolDecStd {
  static bool eqb_dec(bool a, bool b);
  static inline const bool t1 = eqb_dec(true, true);
  static inline const bool t2 = eqb_dec(true, false);
};

#endif // INCLUDED_BOOL_DEC_STD
