#ifndef INCLUDED_QUALIFIED_SHADOW_ASCII
#define INCLUDED_QUALIFIED_SHADOW_ASCII

struct QualifiedShadowAscii {
  struct Shadow {
    enum class shadow { MK };
  };

  static Shadow::shadow id_shadow(Shadow::shadow x);
  static constexpr Shadow::shadow t = Shadow::shadow::MK;
};

#endif // INCLUDED_QUALIFIED_SHADOW_ASCII
