#include "borrow_construction_argument.h"

/// A closure whose only use of a captured/passed value is to read it into a
/// freshly built pair or record is exactly as borrowable as one that only
/// reads it to call another function with it.  ret's fun s => ret (s, a)
/// has the same shape as bind's fun s => k (t s) -- both read s once
/// -- but only bind's style used to be recognised as read-only.  The state
/// monad below models that: ret's continuation builds a pair from the
/// ambient state, and should borrow it exactly as bind's does.
BorrowConstructionArgument::stateT<uint64_t>
BorrowConstructionArgument::test(uint64_t a) {
  return BorrowConstructionArgument::Monad_stateT::template ret<uint64_t>(a);
}

std::pair<uint64_t, BorrowConstructionArgument::big>
BorrowConstructionArgument::run(const BorrowConstructionArgument::big &b) {
  auto [s_, v] = test(UINT64_C(5))(b);
  return std::make_pair(v, std::move(s_));
}
