#include "frame_binder_local_fix_acc.h"

/// Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
/// testing of Crane: the generated program as shrunk by ephyra (hand
/// reduction lost the trigger).
///
/// g1 recurses on a tree; its Node branch calls a local fixpoint whose
/// base case and initial accumulator both call g1 on the left subtree.
/// The explicit-stack frames read acc29, declared only as a member of
/// _after_g1_in_Nil: "use of undeclared identifier 'acc29'".
FrameBinderLocalFixAcc::stream FrameBinderLocalFixAcc::sconst(uint64_t n) {
  return stream::lazy_([=]() -> typename FrameBinderLocalFixAcc::stream::SCons {
    return {n, sconst(n)};
  });
}

FrameBinderLocalFixAcc::stream FrameBinderLocalFixAcc::sfrom(uint64_t n) {
  return stream::lazy_([=]() -> typename FrameBinderLocalFixAcc::stream::SCons {
    return {n, sfrom((n + 1))};
  });
}

List<uint64_t>
FrameBinderLocalFixAcc::stake(uint64_t k,
                              const FrameBinderLocalFixAcc::stream &s) {
  if (k <= 0) {
    return List<uint64_t>::nil();
  } else {
    uint64_t k_ = k - 1;
    const auto &[a0, a1] =
        std::get<typename FrameBinderLocalFixAcc::stream::SCons>(s.v());
    return List<uint64_t>::cons(a0, stake(k_, a1));
  }
}

uint64_t FrameBinderLocalFixAcc::shd(const FrameBinderLocalFixAcc::stream &s) {
  const auto &[a0, _] =
      std::get<typename FrameBinderLocalFixAcc::stream::SCons>(s.v());
  return a0;
}

FrameBinderLocalFixAcc::stream
FrameBinderLocalFixAcc::stl(const FrameBinderLocalFixAcc::stream &s) {
  const auto &[_, a1] =
      std::get<typename FrameBinderLocalFixAcc::stream::SCons>(s.v());
  return a1;
}
