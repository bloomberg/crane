#include "unread_param_captured.h"

String UnreadParamCaptured::op(String u, String) {
  return List<Ascii>::cons(
      Ascii::ascii0(true, false, false, false, false, true, true, false),
      List<Ascii>::cons(
          Ascii::ascii0(false, true, false, false, false, true, true, false),
          List<Ascii>::nil()))
             .template fold_left<String>(
      [=, u = std::move(u)](String, Ascii) {
        auto go =
            [&](const List<std::optional<uint64_t>> &l,
                const String &)
                 -> String {
              // Loop replaces the tail recursion: each recursive call updates
              // the loop variables.
              const List<std::optional<uint64_t>> *_loop_l = &l;
              while (true) {
                if (std::holds_alternative<
                        typename List<std::optional<uint64_t>>::Nil>(
                        _loop_l->v())) {
                  return u;
                } else {
                  const auto &[_, a1] =
                      std::get<typename List<std::optional<uint64_t>>::Cons>(
                          _loop_l->v());
                  _loop_l = crane_raw(a1);
                }
              }
            };
        return go(List<std::optional<uint64_t>>::nil(), u);
      },
      String::string0(
          Ascii::ascii0(false, false, false, true, true, true, true, false),
          String::emptystring()));
}
