#ifndef INCLUDED_BORROW_CONSTRUCTION_ARGUMENT
#define INCLUDED_BORROW_CONSTRUCTION_ARGUMENT

#include "fn.h"
#include "obj.h"
#include <concepts>
#include <cstdint>
#include <utility>

template <typename I>
concept Monad = requires {
  typename I::template m<crane::obj>;
  {
    I::template ret<crane::obj>(std::declval<crane::obj>())
  } -> std::convertible_to<typename I::template m<crane::obj>>;
  {
    I::bind(std::declval<typename I::template m<crane::obj>>(),
            std::declval<
                crane::fn<typename I::template m<crane::obj>(crane::obj)>>())
  } -> std::convertible_to<typename I::template m<crane::obj>>;
};

struct Monad0 {
  template <Monad _tcI0, typename T2>
  static typename _tcI0::template m<T2> ret(const T2 &x);
};

/// A closure whose only use of a captured/passed value is to read it into a
/// freshly built pair or record is exactly as borrowable as one that only
/// reads it to call another function with it.  ret's fun s => ret (s, a)
/// has the same shape as bind's fun s => k (t s) -- both read s once
/// -- but only bind's style used to be recognised as read-only.  The state
/// monad below models that: ret's continuation builds a pair from the
/// ambient state, and should borrow it exactly as bind's does.
struct BorrowConstructionArgument {
  struct big {
    uint64_t b1;
    uint64_t b2;
    uint64_t b3;
    uint64_t b4;
  };

  template <typename a> using stateT = crane::fn<std::pair<big, a>(big)>;

  struct Monad_stateT {
    template <typename CraneA0>
    using m = crane::fn<std::pair<big, CraneA0>(big)>;

    template <typename CraneA0>
    static crane::fn<std::pair<big, CraneA0>(big)> ret(CraneA0 a) {
      return [=](const big &s) { return std::make_pair(s, a); };
    }

    static crane::fn<std::pair<big, crane::obj>(big)>
    bind(crane::fn<std::pair<big, crane::obj>(big)> t,
         crane::fn<crane::fn<std::pair<big, crane::obj>(big)>(crane::obj)> k) {
      return [=](const big &s) {
        auto [s_, v] = t(s);
        return k(v)(std::move(s_));
      };
    }
  };

  static_assert(Monad<Monad_stateT>);
  static stateT<uint64_t> test(uint64_t a);
  static std::pair<uint64_t, big> run(const big &b);
};

template <Monad _tcI0, typename T2>
typename _tcI0::template m<T2> Monad0::ret(const T2 &x) {
  return _tcI0::template ret<T2>(x);
}

#endif // INCLUDED_BORROW_CONSTRUCTION_ARGUMENT
