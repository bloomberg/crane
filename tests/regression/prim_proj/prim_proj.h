#ifndef INCLUDED_PRIM_PROJ
#define INCLUDED_PRIM_PROJ

struct PrimProj {
  struct point {
    uint64_t px;
    uint64_t py;
  };

  static point add_points(const point &p1, const point &p2);
  static inline const point origin = point{UINT64_C(0), UINT64_C(0)};
  static point translate(uint64_t dx, uint64_t dy, const point &p);
};

#endif // INCLUDED_PRIM_PROJ
