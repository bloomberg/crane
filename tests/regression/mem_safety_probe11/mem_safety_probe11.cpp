#include "mem_safety_probe11.h"

unsigned int MemSafetyProbe11::sum_fns(
    const MemSafetyProbe11::mylist<std::function<unsigned int(unsigned int)>>
        &l) {
  if (std::holds_alternative<typename MemSafetyProbe11::mylist<
          std::function<unsigned int(unsigned int)>>::Mynil>(l.v())) {
    return 0u;
  } else {
    const auto &[d_a0, d_a1] = std::get<typename MemSafetyProbe11::mylist<
        std::function<unsigned int(unsigned int)>>::Mycons>(l.v());
    return (d_a0(0u) + sum_fns(*d_a1));
  }
}

/// TEST 1: Accumulate closures that capture BOTH subtrees.
/// Each closure uses tree_sum on both l and r.
/// Both subtrees are also used in recursive calls.
/// After loopification with flatten, the subtrees' unique_ptrs
/// may be moved into continuation frames.
MemSafetyProbe11::mylist<std::function<unsigned int(unsigned int)>>
MemSafetyProbe11::collect_dual_captures(
    const MemSafetyProbe11::tree &t,
    MemSafetyProbe11::mylist<std::function<unsigned int(unsigned int)>> acc) {
  if (std::holds_alternative<typename MemSafetyProbe11::tree::Leaf>(t.v())) {
    return acc;
  } else {
    const auto &[d_a0, d_a1, d_a2] =
        std::get<typename MemSafetyProbe11::tree::Node>(t.v());
    MemSafetyProbe11::tree d_a0_value = *d_a0;
    MemSafetyProbe11::tree d_a2_value = *d_a2;
    MemSafetyProbe11::mylist<std::function<unsigned int(unsigned int)>> acc2 =
        mylist<std::function<unsigned int(unsigned int)>>::mycons(
            [=](auto _xarg0) mutable {
              return _collect_dual_captures_f(_xarg0, d_a0_value, d_a2_value);
            },
            std::move(acc));
    return collect_dual_captures(
        d_a0_value, collect_dual_captures(d_a2_value, std::move(acc2)));
  }
}

/// TEST 2: Closure captures the TAIL of the list (unique_ptr field).
/// Each closure computes length of the tail.
/// After loopification, the tail pointer may be moved.
MemSafetyProbe11::mylist<std::function<unsigned int(unsigned int)>>
MemSafetyProbe11::capture_tails(
    const MemSafetyProbe11::mylist<unsigned int> &l,
    MemSafetyProbe11::mylist<std::function<unsigned int(unsigned int)>> acc) {
  if (std::holds_alternative<
          typename MemSafetyProbe11::mylist<unsigned int>::Mynil>(l.v())) {
    return acc;
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename MemSafetyProbe11::mylist<unsigned int>::Mycons>(
            l.v());
    MemSafetyProbe11::mylist<unsigned int> d_a1_value = *d_a1;
    return capture_tails(
        d_a1_value, mylist<std::function<unsigned int(unsigned int)>>::mycons(
                        [=](auto _xarg0) mutable {
                          return _capture_tails_f(_xarg0, d_a0, d_a1_value);
                        },
                        std::move(acc)));
  }
}

/// TEST 3: Closure captures a SUBTREE, but the subtree is ALSO
/// passed to a recursive call AND used in the continuation.
/// Tests whether the clone/pre-copy mechanism handles triple use.
MemSafetyProbe11::mylist<std::function<unsigned int(unsigned int)>>
MemSafetyProbe11::triple_use_tree(
    const MemSafetyProbe11::tree &t,
    MemSafetyProbe11::mylist<std::function<unsigned int(unsigned int)>> acc) {
  if (std::holds_alternative<typename MemSafetyProbe11::tree::Leaf>(t.v())) {
    return acc;
  } else {
    const auto &[d_a0, d_a1, d_a2] =
        std::get<typename MemSafetyProbe11::tree::Node>(t.v());
    MemSafetyProbe11::tree d_a0_value = *d_a0;
    MemSafetyProbe11::tree d_a2_value = *d_a2;
    MemSafetyProbe11::mylist<std::function<unsigned int(unsigned int)>> acc2 =
        mylist<std::function<unsigned int(unsigned int)>>::mycons(
            [=](auto _xarg0) mutable {
              return _triple_use_tree_fr(_xarg0, d_a2_value);
            },
            mylist<std::function<unsigned int(unsigned int)>>::mycons(
                [=](auto _xarg0) mutable {
                  return _triple_use_tree_fl(_xarg0, d_a0_value);
                },
                std::move(acc)));
    return triple_use_tree(d_a0_value,
                           triple_use_tree(d_a2_value, std::move(acc2)));
  }
}

/// TEST 5: Tail-recursive function with two accumulators,
/// one of which stores closures that capture the other.
/// Tests whether accumulator values are properly captured.
MemSafetyProbe11::mylist<std::function<unsigned int(unsigned int)>>
MemSafetyProbe11::dual_accum(
    const MemSafetyProbe11::mylist<unsigned int> &l, unsigned int sum_acc,
    MemSafetyProbe11::mylist<std::function<unsigned int(unsigned int)>>
        fn_acc) {
  if (std::holds_alternative<
          typename MemSafetyProbe11::mylist<unsigned int>::Mynil>(l.v())) {
    return fn_acc;
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename MemSafetyProbe11::mylist<unsigned int>::Mycons>(
            l.v());
    MemSafetyProbe11::mylist<unsigned int> d_a1_value = *d_a1;
    unsigned int new_sum = (sum_acc + d_a0);
    return dual_accum(
        d_a1_value, new_sum,
        mylist<std::function<unsigned int(unsigned int)>>::mycons(
            [=](auto _xarg0) mutable { return _dual_accum_f(_xarg0, new_sum); },
            std::move(fn_acc)));
  }
}
