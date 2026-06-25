#ifndef INCLUDED_SLLPAIRCASTDEQUE
#define INCLUDED_SLLPAIRCASTDEQUE

#include <any>
#include <deque>
#include <memory>
#include <optional>
#include <utility>

namespace SllPairCastDeque {

struct SllPairCastDeque {
  struct sll_frame {
    std::optional<uint64_t> fr_ret;
    std::deque<uint64_t> fr_suf;
  };

  using sll_stack = std::pair<sll_frame, std::deque<sll_frame>>;

  struct sll_subparser {
    std::deque<uint64_t> sll_pred;
    sll_stack sll_stk;
  };

  static bool sll_final_config(const sll_subparser &sp);

  static const bool &test_final() {
    static const bool v = sll_final_config(
        sll_subparser{[](auto _a0, auto _a1) {
                        _a1.push_front(_a0);
                        return _a1;
                      }(UINT64_C(1),
                        [](auto _a0, auto _a1) {
                          _a1.push_front(_a0);
                          return _a1;
                        }(UINT64_C(2), std::deque<uint64_t>{})),
                      std::make_pair(sll_frame{std::optional<uint64_t>(),
                                               std::deque<uint64_t>{}},
                                     std::deque<sll_frame>{})});
    return v;
  }

  static const bool &test_not_final() {
    static const bool v = sll_final_config(sll_subparser{
        std::deque<uint64_t>{},
        std::make_pair(
            sll_frame{std::make_optional<uint64_t>(UINT64_C(5)),
                      [](auto _a0, auto _a1) {
                        _a1.push_front(_a0);
                        return _a1;
                      }(UINT64_C(1), std::deque<uint64_t>{})},
            [](auto _a0, auto _a1) {
              _a1.push_front(_a0);
              return _a1;
            }(sll_frame{std::optional<uint64_t>(), std::deque<uint64_t>{}},
              std::deque<sll_frame>{}))});
    return v;
  }
};

} // namespace SllPairCastDeque

#endif // INCLUDED_SLLPAIRCASTDEQUE
