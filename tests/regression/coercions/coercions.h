#ifndef INCLUDED_COERCIONS
#define INCLUDED_COERCIONS

#include <functional>

struct Coercions {
  static uint64_t bool_to_nat(bool b);
  static uint64_t add_bool(uint64_t n, bool b);
  static inline const uint64_t test_add_true = add_bool(UINT64_C(5), true);
  static inline const uint64_t test_add_false = add_bool(UINT64_C(5), false);

  struct Wrapper {
    uint64_t unwrap;

    // ACCESSORS
    Wrapper clone() const { return Wrapper{(*this).unwrap}; }
  };

  static uint64_t double_wrapped(const Wrapper &w);
  static inline const uint64_t test_double_wrapped =
      double_wrapped(Wrapper{UINT64_C(7)});

  struct BoolBox {
    bool unbox;

    // ACCESSORS
    BoolBox clone() const { return BoolBox{(*this).unbox}; }
  };

  static uint64_t add_boolbox(uint64_t n, const BoolBox &bb);
  static inline const uint64_t test_add_boolbox =
      add_boolbox(UINT64_C(10), BoolBox{true});

  struct Transform {
    std::function<uint64_t(uint64_t)> apply_transform;

    // ACCESSORS
    Transform clone() const { return Transform{(*this).apply_transform}; }
  };

  static inline const Transform double_transform =
      Transform{[](uint64_t n) { return (n + n); }};
  static inline const uint64_t test_fun_coercion =
      double_transform.apply_transform(UINT64_C(5));
};

#endif // INCLUDED_COERCIONS
