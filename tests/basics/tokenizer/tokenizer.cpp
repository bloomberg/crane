#include "tokenizer.h"

std::pair<std::optional<std::basic_string_view<char>>,
          std::basic_string_view<char>>
Tokenizer::next_token(std::basic_string_view<char> input,
                      std::basic_string_view<char> soft,
                      std::basic_string_view<char> hard) {
  {
    uint64_t _lc1_fuel = static_cast<uint64_t>(input.length());
    int64_t _lc1_index = INT64_C(0);
    std::basic_string_view<char> _lc1_s = input;
    std::basic_string_view<char> _lc1_loop_s = std::move(_lc1_s);
    int64_t _lc1_loop_index = _lc1_index;
    uint64_t _lc1_loop_fuel = _lc1_fuel;
    while (true) {
      if (_lc1_loop_s.length() == INT64_C(0)) {
        return std::make_pair(std::optional<std::basic_string_view<char>>(),
                              std::string_view(nullptr, 0));
      } else {
        if (_lc1_loop_fuel <= 0) {
          return std::make_pair(
              std::make_optional<std::basic_string_view<char>>(_lc1_loop_s),
              std::string_view(nullptr, 0));
        } else {
          uint64_t fuel_ = _lc1_loop_fuel - 1;
          char c =
              ((_lc1_loop_index >= 0 &&
                _lc1_loop_index < static_cast<int64_t>(_lc1_loop_s.length()))
                   ? _lc1_loop_s[_lc1_loop_index]
                   : static_cast<char>(0));
          if (hard.contains(c)) {
            auto &&_once1 =
                static_cast<int64_t>((static_cast<uint64_t>(_lc1_loop_index) +
                                      static_cast<uint64_t>(INT64_C(1))) &
                                     0x7FFFFFFFFFFFFFFFULL);
            return std::make_pair(
                std::make_optional<std::basic_string_view<char>>(
                    ((INT64_C(0) >= 0 &&
                      INT64_C(0) <= static_cast<int64_t>(_lc1_loop_s.length()))
                         ? _lc1_loop_s.substr(INT64_C(0), _lc1_loop_index)
                         : std::basic_string_view<char>())),
                ((_once1 >= 0 &&
                  _once1 <= static_cast<int64_t>(_lc1_loop_s.length()))
                     ? _lc1_loop_s.substr(
                           _once1,
                           static_cast<int64_t>(
                               (static_cast<uint64_t>(input.length()) -
                                static_cast<uint64_t>(static_cast<int64_t>(
                                    (static_cast<uint64_t>(_lc1_loop_index) +
                                     static_cast<uint64_t>(INT64_C(1))) &
                                    0x7FFFFFFFFFFFFFFFULL))) &
                               0x7FFFFFFFFFFFFFFFULL))
                     : std::basic_string_view<char>()));
          } else {
            if (soft.contains(c)) {
              if (_lc1_loop_index == INT64_C(0)) {
                _lc1_loop_s =
                    ((INT64_C(1) >= 0 &&
                      INT64_C(1) <= static_cast<int64_t>(_lc1_loop_s.length()))
                         ? _lc1_loop_s.substr(
                               INT64_C(1),
                               static_cast<int64_t>(
                                   (static_cast<uint64_t>(input.length()) -
                                    static_cast<uint64_t>(INT64_C(1))) &
                                   0x7FFFFFFFFFFFFFFFULL))
                         : std::basic_string_view<char>());
                _lc1_loop_index = INT64_C(0);
                _lc1_loop_fuel = fuel_;
              } else {
                auto &&_once2 = static_cast<int64_t>(
                    (static_cast<uint64_t>(_lc1_loop_index) +
                     static_cast<uint64_t>(INT64_C(1))) &
                    0x7FFFFFFFFFFFFFFFULL);
                return std::make_pair(
                    std::make_optional<std::basic_string_view<char>>(
                        ((INT64_C(0) >= 0 &&
                          INT64_C(0) <=
                              static_cast<int64_t>(_lc1_loop_s.length()))
                             ? _lc1_loop_s.substr(INT64_C(0), _lc1_loop_index)
                             : std::basic_string_view<char>())),
                    ((_once2 >= 0 &&
                      _once2 <= static_cast<int64_t>(_lc1_loop_s.length()))
                         ? _lc1_loop_s.substr(
                               _once2,
                               static_cast<int64_t>(
                                   (static_cast<uint64_t>(input.length()) -
                                    static_cast<uint64_t>(static_cast<int64_t>(
                                        (static_cast<uint64_t>(
                                             _lc1_loop_index) +
                                         static_cast<uint64_t>(INT64_C(1))) &
                                        0x7FFFFFFFFFFFFFFFULL))) &
                                   0x7FFFFFFFFFFFFFFFULL))
                         : std::basic_string_view<char>()));
              }
            } else {
              _lc1_loop_index =
                  static_cast<int64_t>((static_cast<uint64_t>(_lc1_loop_index) +
                                        static_cast<uint64_t>(INT64_C(1))) &
                                       0x7FFFFFFFFFFFFFFFULL);
              _lc1_loop_fuel = fuel_;
            }
          }
        }
      }
    }
  }
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
          t = next_token(std::move(rest), soft, hard);
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
  {
    uint64_t _lc1_fuel = static_cast<uint64_t>(input.length());
    std::basic_string_view<char> _lc1_rest = std::move(input);
    return aux_impl(aux_impl, _lc1_fuel, std::move(_lc1_rest));
  }
}
