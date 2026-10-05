#include "tokenizer.h"

std::pair<std::optional<std::basic_string_view<char>>,
          std::basic_string_view<char>>
Tokenizer::next_token(std::basic_string_view<char> input,
                      std::basic_string_view<char> soft,
                      std::basic_string_view<char> hard) {
  auto aux = [&](uint64_t fuel, int64_t index, std::basic_string_view<char> s)
      -> std::pair<std::optional<std::basic_string_view<char>>,
                   std::basic_string_view<char>> {
    std::basic_string_view<char> _loop_s = std::move(s);
    int64_t _loop_index = std::move(index);
    uint64_t _loop_fuel = std::move(fuel);
    while (true) {
      if (_loop_s.length() == INT64_C(0)) {
        return std::make_pair(std::optional<std::basic_string_view<char>>(),
                              std::string_view(nullptr, 0));
      } else {
        if (_loop_fuel <= 0) {
          return std::make_pair(
              std::make_optional<std::basic_string_view<char>>(_loop_s),
              std::string_view(nullptr, 0));
        } else {
          uint64_t fuel_ = _loop_fuel - 1;
          char c = ((_loop_index >= 0 &&
                     _loop_index < static_cast<int64_t>(_loop_s.length()))
                        ? _loop_s[_loop_index]
                        : static_cast<char>(0));
          if (hard.contains(c)) {
            return std::make_pair(
                std::make_optional<std::basic_string_view<char>>(
                    ((INT64_C(0) >= 0 &&
                      INT64_C(0) <= static_cast<int64_t>(_loop_s.length()))
                         ? _loop_s.substr(INT64_C(0), _loop_index)
                         : std::basic_string_view<char>())),
                ((static_cast<int64_t>((static_cast<uint64_t>(_loop_index) +
                                        static_cast<uint64_t>(INT64_C(1))) &
                                       0x7FFFFFFFFFFFFFFFULL) >= 0 &&
                  static_cast<int64_t>((static_cast<uint64_t>(_loop_index) +
                                        static_cast<uint64_t>(INT64_C(1))) &
                                       0x7FFFFFFFFFFFFFFFULL) <=
                      static_cast<int64_t>(_loop_s.length()))
                     ? _loop_s.substr(
                           static_cast<int64_t>(
                               (static_cast<uint64_t>(_loop_index) +
                                static_cast<uint64_t>(INT64_C(1))) &
                               0x7FFFFFFFFFFFFFFFULL),
                           static_cast<int64_t>(
                               (static_cast<uint64_t>(input.length()) -
                                static_cast<uint64_t>(static_cast<int64_t>(
                                    (static_cast<uint64_t>(_loop_index) +
                                     static_cast<uint64_t>(INT64_C(1))) &
                                    0x7FFFFFFFFFFFFFFFULL))) &
                               0x7FFFFFFFFFFFFFFFULL))
                     : std::basic_string_view<char>()));
          } else {
            if (soft.contains(c)) {
              if (_loop_index == INT64_C(0)) {
                _loop_s =
                    ((INT64_C(1) >= 0 &&
                      INT64_C(1) <= static_cast<int64_t>(_loop_s.length()))
                         ? _loop_s.substr(
                               INT64_C(1),
                               static_cast<int64_t>(
                                   (static_cast<uint64_t>(input.length()) -
                                    static_cast<uint64_t>(INT64_C(1))) &
                                   0x7FFFFFFFFFFFFFFFULL))
                         : std::basic_string_view<char>());
                _loop_index = INT64_C(0);
                _loop_fuel = fuel_;
              } else {
                return std::make_pair(
                    std::make_optional<std::basic_string_view<char>>(
                        ((INT64_C(0) >= 0 &&
                          INT64_C(0) <= static_cast<int64_t>(_loop_s.length()))
                             ? _loop_s.substr(INT64_C(0), _loop_index)
                             : std::basic_string_view<char>())),
                    ((static_cast<int64_t>((static_cast<uint64_t>(_loop_index) +
                                            static_cast<uint64_t>(INT64_C(1))) &
                                           0x7FFFFFFFFFFFFFFFULL) >= 0 &&
                      static_cast<int64_t>((static_cast<uint64_t>(_loop_index) +
                                            static_cast<uint64_t>(INT64_C(1))) &
                                           0x7FFFFFFFFFFFFFFFULL) <=
                          static_cast<int64_t>(_loop_s.length()))
                         ? _loop_s.substr(
                               static_cast<int64_t>(
                                   (static_cast<uint64_t>(_loop_index) +
                                    static_cast<uint64_t>(INT64_C(1))) &
                                   0x7FFFFFFFFFFFFFFFULL),
                               static_cast<int64_t>(
                                   (static_cast<uint64_t>(input.length()) -
                                    static_cast<uint64_t>(static_cast<int64_t>(
                                        (static_cast<uint64_t>(_loop_index) +
                                         static_cast<uint64_t>(INT64_C(1))) &
                                        0x7FFFFFFFFFFFFFFFULL))) &
                                   0x7FFFFFFFFFFFFFFFULL))
                         : std::basic_string_view<char>()));
              }
            } else {
              _loop_index =
                  static_cast<int64_t>((static_cast<uint64_t>(_loop_index) +
                                        static_cast<uint64_t>(INT64_C(1))) &
                                       0x7FFFFFFFFFFFFFFFULL);
              _loop_fuel = fuel_;
            }
          }
        }
      }
    }
  };
  return aux(static_cast<uint64_t>(input.length()), INT64_C(0), input);
}

List<std::basic_string_view<char>>
Tokenizer::list_tokens(std::basic_string_view<char> input,
                       std::basic_string_view<char> soft,
                       std::basic_string_view<char> hard) {
  auto aux_impl = [&](auto &_self_aux, uint64_t fuel,
                      std::basic_string_view<char> rest)
      -> List<std::basic_string_view<char>> {
    if (fuel <= 0) {
      return List<std::basic_string_view<char>>::nil();
    } else {
      uint64_t fuel_ = fuel - 1;
      std::pair<std::optional<std::basic_string_view<char>>,
                std::basic_string_view<char>>
          t = next_token(rest, soft, hard);
      auto _cs = t.first;
      if (_cs.has_value()) {
        const std::basic_string_view<char> &t_ = *_cs;
        return List<std::basic_string_view<char>>::cons(
            t_, _self_aux(_self_aux, fuel_, std::move(t).second));
      } else {
        return List<std::basic_string_view<char>>::nil();
      }
    }
  };
  auto aux = [&](uint64_t fuel, std::basic_string_view<char> rest)
      -> List<std::basic_string_view<char>> {
    return aux_impl(aux_impl, fuel, rest);
  };
  return aux(static_cast<uint64_t>(input.length()), input);
}
