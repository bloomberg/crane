#include "dependent_choice_continuation.h"

bool DependentChoiceContinuation::run(
    const DependentChoiceContinuation::MemS<bool> &m) {
  if (std::holds_alternative<
          typename DependentChoiceContinuation::MemS<bool>::MRet>(m.v())) {
    const auto &[a0] =
        std::get<typename DependentChoiceContinuation::MemS<bool>::MRet>(m.v());
    return a0;
  } else {
    const auto &[c0, k0] =
        std::get<typename DependentChoiceContinuation::MemS<bool>::Mchoose>(
            m.v());
    switch (c0) {
    case MemC::CNEXT_KEY: {
      return false;
    }
    case MemC::CFRESH_PROV: {
      auto &&_sv0 = k0(true);
      if (std::holds_alternative<
              typename DependentChoiceContinuation::MemS<bool>::MRet>(
              _sv0.v())) {
        const auto &[a0] =
            std::get<typename DependentChoiceContinuation::MemS<bool>::MRet>(
                _sv0.v());
        return a0;
      } else {
        return false;
      }
      break;
    }
    default:
      std::unreachable();
    }
  }
}
