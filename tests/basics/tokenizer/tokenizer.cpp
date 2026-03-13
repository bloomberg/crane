#include <tokenizer.h>

#include <algorithm>
#include <any>
#include <cassert>
#include <cstdint>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <string_view>
#include <utility>
#include <variant>
#include <vector>

__attribute__((pure)) std::pair<std::optional<std::basic_string_view<char>>,
                                std::basic_string_view<char>>
Tokenizer::next_token(const std::basic_string_view<char> input,
                      const std::basic_string_view<char> soft,
                      const std::basic_string_view<char> hard) {
  std::function<std::pair<std::optional<std::basic_string_view<char>>,
                          std::basic_string_view<char>>(
      unsigned int, int64_t, std::basic_string_view<char>)>
      aux;
  aux = [&](unsigned int fuel, int64_t index, std::basic_string_view<char> s)
      -> std::pair<std::optional<std::basic_string_view<char>>,
                   std::basic_string_view<char>> {
    if (s.length() == int64_t(0)) {
      return std::make_pair(std::nullopt, std::string_view(nullptr, 0));
    } else {
      if (fuel <= 0) {
        return std::make_pair(
            std::make_optional<std::basic_string_view<char>>(s),
            std::string_view(nullptr, 0));
      } else {
        unsigned int fuel_ = fuel - 1;
        int64_t c = s[index];
        if (hard.contains(c)) {
          return std::make_pair(
              std::make_optional<std::basic_string_view<char>>(
                  s.substr(int64_t(0), index)),
              s.substr(((index + int64_t(1)) & 0x7FFFFFFFFFFFFFFFLL),
                       ((input.length() -
                         ((index + int64_t(1)) & 0x7FFFFFFFFFFFFFFFLL)) &
                        0x7FFFFFFFFFFFFFFFLL)));
        } else {
          if (soft.contains(c)) {
            if (index == int64_t(0)) {
              return aux(fuel_, int64_t(0),
                         s.substr(int64_t(1), ((input.length() - int64_t(1)) &
                                               0x7FFFFFFFFFFFFFFFLL)));
            } else {
              return std::make_pair(
                  std::make_optional<std::basic_string_view<char>>(
                      s.substr(int64_t(0), index)),
                  s.substr(((index + int64_t(1)) & 0x7FFFFFFFFFFFFFFFLL),
                           ((input.length() -
                             ((index + int64_t(1)) & 0x7FFFFFFFFFFFFFFFLL)) &
                            0x7FFFFFFFFFFFFFFFLL)));
            }
          } else {
            return aux(fuel_, ((index + int64_t(1)) & 0x7FFFFFFFFFFFFFFFLL), s);
          }
        }
      }
    }
  };
  return aux(static_cast<unsigned int>(input.length()), int64_t(0), input);
}

std::shared_ptr<List<std::basic_string_view<char>>>
Tokenizer::list_tokens(const std::basic_string_view<char> input,
                       const std::basic_string_view<char> soft,
                       const std::basic_string_view<char> hard) {
  std::function<std::shared_ptr<List<std::basic_string_view<char>>>(
      unsigned int, std::basic_string_view<char>)>
      aux;
  aux = [&](unsigned int fuel, std::basic_string_view<char> rest)
      -> std::shared_ptr<List<std::basic_string_view<char>>> {
    if (fuel <= 0) {
      return List<std::basic_string_view<char>>::ctor::Nil_();
    } else {
      unsigned int fuel_ = fuel - 1;
      std::pair<std::optional<std::basic_string_view<char>>,
                std::basic_string_view<char>>
          t = next_token(rest, soft, hard);
      if (t.first.has_value()) {
        std::basic_string_view<char> t_ = *t.first;
        return List<std::basic_string_view<char>>::ctor::Cons_(
            std::move(t_), aux(fuel_, t.second));
      } else {
        return List<std::basic_string_view<char>>::ctor::Nil_();
      }
    }
  };
  return aux(static_cast<unsigned int>(input.length()), input);
}
