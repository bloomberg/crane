#ifndef INCLUDED_QUALIFIED_SHADOW_ASCII
#define INCLUDED_QUALIFIED_SHADOW_ASCII

struct QualifiedShadowAscii {
  struct Shadow {
    enum class shadow { e_MK };
  };

  static Shadow::shadow id_shadow(Shadow::shadow x);
  static inline const Shadow::shadow t = id_shadow(Shadow::shadow::e_MK);
};

#endif // INCLUDED_QUALIFIED_SHADOW_ASCII
