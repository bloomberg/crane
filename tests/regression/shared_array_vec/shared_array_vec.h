#ifndef INCLUDED_SHARED_ARRAY_VEC
#define INCLUDED_SHARED_ARRAY_VEC

#include <conslist.h>
#include <cstdint>
#include <shared_array.h>
#include <utility>

struct List {
  template <typename T1, typename T2, typename F0>
  static T1 fold_left(F0 &&f, const crane::list<T2> &l, T1 a0);
};

struct ListDef {
  template <typename T1, typename T2, typename F0>
  static crane::list<T2> map(F0 &&f, const crane::list<T1> &l);
};

struct SharedArrayVec {
  template <typename T1, typename T2, typename F1>
  static T2 vec_rect(T2 f, F1 &&f0, const crane::shared_array<T1> &v) {
    if (v.empty()) {
      return f;
    } else {
      const T1 &y = v.front();
      auto v0 = v.drop(1);
      return f0(y, v0, vec_rect<T1, T2>(std::move(f), f0, v0));
    }
  }

  template <typename T1, typename T2, typename F1>
  static T2 vec_rec(T2 f, F1 &&f0, const crane::shared_array<T1> &v) {
    return vec_rect<T1, T2>(std::move(f), f0, v);
  }

  template <typename T1>
  static T1 vec_nth(const crane::shared_array<T1> &v, uint64_t n, T1 d) {
    if (v.empty()) {
      return d;
    } else {
      const T1 &h = v.front();
      auto t = v.drop(1);
      if (n <= 0) {
        return h;
      } else {
        uint64_t m = n - 1;
        return vec_nth<T1>(t, m, std::move(d));
      }
    }
  }

  static uint64_t vec_sum(const crane::shared_array<uint64_t> &v);
  static inline const crane::shared_array<crane::shared_array<uint64_t>> table =
      crane::shared_array<crane::shared_array<uint64_t>>::of_range(
          ListDef::template map<crane::list<uint64_t>,
                                crane::shared_array<uint64_t>>(
              [](crane::list<uint64_t> _x0) -> crane::shared_array<uint64_t> {
                return crane::shared_array<uint64_t>::of_range(_x0);
              },
              crane::cons(
                  crane::cons(
                      UINT64_C(1),
                      crane::cons(
                          UINT64_C(2),
                          crane::cons(UINT64_C(3), crane::list<uint64_t>{}))),
                  crane::cons(
                      crane::cons(
                          UINT64_C(4),
                          crane::cons(UINT64_C(5), crane::list<uint64_t>{})),
                      crane::cons(
                          crane::list<uint64_t>{},
                          crane::cons(
                              crane::cons(UINT64_C(6), crane::list<uint64_t>{}),
                              crane::list<crane::list<uint64_t>>{}))))));
  static inline const crane::list<
      crane::shared_array<crane::shared_array<uint64_t>>>
      copies = crane::cons(
          table,
          crane::cons(
              table,
              crane::cons(
                  table.push_front(crane::shared_array<uint64_t>::of_range(
                      crane::cons(UINT64_C(7), crane::list<uint64_t>{}))),
                  crane::list<
                      crane::shared_array<crane::shared_array<uint64_t>>>{})));
  static inline const uint64_t result =
      (((vec_nth<uint64_t>(
             vec_nth<crane::shared_array<uint64_t>>(
                 table, UINT64_C(1), crane::shared_array<uint64_t>{}),
             UINT64_C(1), UINT64_C(0)) +
         vec_nth<uint64_t>(
             vec_nth<crane::shared_array<uint64_t>>(
                 table, UINT64_C(2), crane::shared_array<uint64_t>{}),
             UINT64_C(0), UINT64_C(100))) +
        vec_sum(vec_nth<crane::shared_array<uint64_t>>(
            table, UINT64_C(0), crane::shared_array<uint64_t>{}))) +
       List::template fold_left<
           uint64_t, crane::shared_array<crane::shared_array<uint64_t>>>(
           [](uint64_t acc,
              const crane::shared_array<crane::shared_array<uint64_t>> &t) {
             return (acc +
                     vec_sum(vec_nth<crane::shared_array<uint64_t>>(
                         t, UINT64_C(0), crane::shared_array<uint64_t>{})));
           },
           copies, UINT64_C(0)));
};

template <typename T1, typename T2, typename F0>
T1 List::fold_left(F0 &&f, const crane::list<T2> &l, T1 a0) {
  if (l.empty()) {
    return a0;
  } else {
    const T2 &b = l.front();
    auto l0 = l.tail();
    return List::template fold_left<T1, T2>(f, l0, f(std::move(a0), b));
  }
}

template <typename T1, typename T2, typename F0>
crane::list<T2> ListDef::map(F0 &&f, const crane::list<T1> &l) {
  if (l.empty()) {
    return crane::list<T2>{};
  } else {
    const T1 &a = l.front();
    auto l0 = l.tail();
    return crane::cons(f(a), ListDef::template map<T1, T2>(f, l0));
  }
}

#endif // INCLUDED_SHARED_ARRAY_VEC
