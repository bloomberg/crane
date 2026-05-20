#ifndef INCLUDED_ROCQ_BUG_14843
#define INCLUDED_ROCQ_BUG_14843

#include <functional>

enum class Unit { TT };

struct RocqBug14843 {
  struct r {
    std::function<void(Unit)> f1;
    std::function<void(Unit)> f2;

    // ACCESSORS
    r clone() const { return r{this->f1, this->f2}; }
  };

  struct r_ {
    std::function<void(Unit)> f1_;
    std::function<void(Unit)> f2_;

    // ACCESSORS
    r_ clone() const { return r_{this->f1_, this->f2_}; }
  };

  struct M {
    static void f1(Unit _x);
    static void f2(Unit _x);
    static inline const r cf = r{f1, f2};
    static void f1_(Unit _x);
    static void f2_(Unit _x);
    static inline const r_ cf_ = r_{f1_, f2_};
  };
};

#endif // INCLUDED_ROCQ_BUG_14843
