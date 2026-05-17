#ifndef INCLUDED_IDENTIFIER_ESCAPE_PARAM
#define INCLUDED_IDENTIFIER_ESCAPE_PARAM

struct IdentifierEscapeParam {
  static unsigned int id_from_param(unsigned int double0);
  static unsigned int add_one_from_param(unsigned int double0);
  static inline const unsigned int t = add_one_from_param(6u);
};

#endif // INCLUDED_IDENTIFIER_ESCAPE_PARAM
