#include "mem_safety_probe11.h"

unsigned int MemSafetyProbe11::sum_fns(
    const MemSafetyProbe11::mylist<std::function<unsigned int(unsigned int)>>
        &l) {
  if (std::holds_alternative<typename MemSafetyProbe11::mylist<
          std::function<unsigned int(unsigned int)>>::Mynil>(l.v())) {
    return 0u;
  } else {
    const auto &[a0, a1] = std::get<typename MemSafetyProbe11::mylist<
        std::function<unsigned int(unsigned int)>>::Mycons>(l.v());
    return (a0(0u) + sum_fns(*a1));
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
    const auto &[a0, a1, a2] =
        std::get<typename MemSafetyProbe11::tree::Node>(t.v());
    const MemSafetyProbe11::tree &a0_value = *a0;
    const MemSafetyProbe11::tree &a2_value = *a2;
    MemSafetyProbe11::mylist<std::function<unsigned int(unsigned int)>> acc2 =
        mylist<std::function<unsigned int(unsigned int)>>::mycons(
            [=](auto _xarg0) mutable {
              return _collect_dual_captures_f(_xarg0, a0_value, a2_value);
            },
            std::move(acc));
    return collect_dual_captures(
        a0_value, collect_dual_captures(a2_value, std::move(acc2)));
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
    const auto &[a0, a1] =
        std::get<typename MemSafetyProbe11::mylist<unsigned int>::Mycons>(
            l.v());
    const MemSafetyProbe11::mylist<unsigned int> &a1_value = *a1;
    return capture_tails(
        a1_value, mylist<std::function<unsigned int(unsigned int)>>::mycons(
                      [=](auto _xarg0) mutable {
                        return _capture_tails_f(_xarg0, a0, a1_value);
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
    const auto &[a0, a1, a2] =
        std::get<typename MemSafetyProbe11::tree::Node>(t.v());
    const MemSafetyProbe11::tree &a0_value = *a0;
    const MemSafetyProbe11::tree &a2_value = *a2;
    MemSafetyProbe11::mylist<std::function<unsigned int(unsigned int)>> acc2 =
        mylist<std::function<unsigned int(unsigned int)>>::mycons(
            [=](auto _xarg0) mutable {
              return _triple_use_tree_fr(_xarg0, a2_value);
            },
            mylist<std::function<unsigned int(unsigned int)>>::mycons(
                [=](auto _xarg0) mutable {
                  return _triple_use_tree_fl(_xarg0, a0_value);
                },
                std::move(acc)));
    return triple_use_tree(a0_value,
                           triple_use_tree(a2_value, std::move(acc2)));
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
    const auto &[a0, a1] =
        std::get<typename MemSafetyProbe11::mylist<unsigned int>::Mycons>(
            l.v());
    const MemSafetyProbe11::mylist<unsigned int> &a1_value = *a1;
    unsigned int new_sum = (sum_acc + a0);
    return dual_accum(
        a1_value, new_sum,
        mylist<std::function<unsigned int(unsigned int)>>::mycons(
            [=](auto _xarg0) mutable { return _dual_accum_f(_xarg0, new_sum); },
            std::move(fn_acc)));
  }
}
