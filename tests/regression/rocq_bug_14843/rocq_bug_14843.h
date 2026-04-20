#ifndef INCLUDED_ROCQ_BUG_14843
#define INCLUDED_ROCQ_BUG_14843

#include <functional>
#include <memory>
#include <type_traits>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

enum class Unit { e_TT };

struct RocqBug14843 {
  struct r {
    std::function<void(Unit)> f1;
    std::function<void(Unit)> f2;
  };

  struct r_ {
    std::function<void(Unit)> f1_;
    std::function<void(Unit)> f2_;
  };

  struct M {
    static void f1(const Unit _x);
    static void f2(const Unit _x);
    static inline const std::shared_ptr<r> cf = std::make_shared<r>(r{f1, f2});
    static void f1_(const Unit _x);
    static void f2_(const Unit _x);
    static inline const std::shared_ptr<r_> cf_ =
        std::make_shared<r_>(r_{f1_, f2_});
  };
};

#endif // INCLUDED_ROCQ_BUG_14843
