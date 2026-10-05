#ifndef INCLUDED_BOOL_DEC_STD
#define INCLUDED_BOOL_DEC_STD

struct Bool {
  static bool bool_dec(bool b1, bool b2);
};

struct BoolDecStd {
  static bool eqb_dec(bool a, bool b);
  static constexpr bool t1 = true;
  static constexpr bool t2 = false;
};

#endif // INCLUDED_BOOL_DEC_STD
