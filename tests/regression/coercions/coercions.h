#ifndef INCLUDED_COERCIONS
#define INCLUDED_COERCIONS

#include <functional>

struct Coercions {
  static unsigned int bool_to_nat(bool b);
  static unsigned int add_bool(unsigned int n, bool b);
  static inline const unsigned int test_add_true = add_bool(5u, true);
  static inline const unsigned int test_add_false = add_bool(5u, false);

  struct Wrapper {
    unsigned int unwrap;

    // ACCESSORS
    Wrapper clone() const { return Wrapper{(*this).unwrap}; }
  };

  static unsigned int double_wrapped(const Wrapper &w);
  static inline const unsigned int test_double_wrapped =
      double_wrapped(Wrapper{7u});

  struct BoolBox {
    bool unbox;

    // ACCESSORS
    BoolBox clone() const { return BoolBox{(*this).unbox}; }
  };

  static unsigned int add_boolbox(unsigned int n, const BoolBox &bb);
  static inline const unsigned int test_add_boolbox =
      add_boolbox(10u, BoolBox{true});

  struct Transform {
    std::function<unsigned int(unsigned int)> apply_transform;

    // ACCESSORS
    Transform clone() const { return Transform{(*this).apply_transform}; }
  };

  static inline const Transform double_transform =
      Transform{[](unsigned int n) { return (n + n); }};
  static inline const unsigned int test_fun_coercion =
      double_transform.apply_transform(5u);
};

#endif // INCLUDED_COERCIONS
