#ifndef INCLUDED_PRIM_PROJ
#define INCLUDED_PRIM_PROJ

struct PrimProj {
  struct point {
    unsigned int px;
    unsigned int py;

    // ACCESSORS
    point clone() const { return point{(*this).px, (*this).py}; }
  };

  static point add_points(const point &p1, const point &p2);
  static inline const point origin = point{0u, 0u};
  static point translate(unsigned int dx, unsigned int dy, const point &p);
};

#endif // INCLUDED_PRIM_PROJ
