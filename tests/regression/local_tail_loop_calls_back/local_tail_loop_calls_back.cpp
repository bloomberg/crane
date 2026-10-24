#include "local_tail_loop_calls_back.h"

std::optional<uint64_t>
LocalTailLoopCallsBack::find(const LocalTailLoopCallsBack::tree &t,
                             uint64_t k) {
  auto scan = [](const List<LocalTailLoopCallsBack::tree> &ts,
                 uint64_t k0) -> std::optional<uint64_t> {
    uint64_t _loop_k0 = k0;
    const List<LocalTailLoopCallsBack::tree> *_loop_ts = &ts;
    while (true) {
      if (std::holds_alternative<
              typename List<LocalTailLoopCallsBack::tree>::Nil>(
              _loop_ts->v())) {
        return std::optional<uint64_t>();
      } else {
        const auto &[a0, a1] =
            std::get<typename List<LocalTailLoopCallsBack::tree>::Cons>(
                _loop_ts->v());
        if (_loop_k0 == UINT64_C(0)) {
          return find(a0, _loop_k0);
        } else {
          _loop_k0 = (((_loop_k0 - UINT64_C(1)) > _loop_k0
                           ? 0
                           : (_loop_k0 - UINT64_C(1))));
          _loop_ts = crane_raw(a1);
        }
      }
    }
  };
  if (std::holds_alternative<typename LocalTailLoopCallsBack::tree::Leaf>(
          t.v())) {
    const auto &[n0] =
        std::get<typename LocalTailLoopCallsBack::tree::Leaf>(t.v());
    return std::make_optional<uint64_t>(n0);
  } else {
    const auto &[ts0] =
        std::get<typename LocalTailLoopCallsBack::tree::Node>(t.v());
    return scan(*ts0, k);
  }
}
