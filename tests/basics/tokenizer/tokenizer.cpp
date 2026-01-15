#include <algorithm>
#include <fstream>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <string>
#include <string_view>
#include <tokenizer.h>
#include <utility>
#include <variant>
#include <vector>

std::pair<std::optional<std::basic_string_view<char>>,
          std::basic_string_view<char>>
Tokenizer::next_token(const std::basic_string_view<char> input,
                      const std::basic_string_view<char> soft,
                      const std::basic_string_view<char> hard) {
  std::function<std::pair<std::optional<std::basic_string_view<char>>,
                          std::basic_string_view<char>>(
      unsigned int, int, std::basic_string_view<char>)>
      aux;
  aux = [&](unsigned int fuel, int index, std::basic_string_view<char> s)
      -> std::pair<std::optional<std::basic_string_view<char>>,
                   std::basic_string_view<char>> {
    if (s.length() == 0) {
      return std::make_pair(std::nullopt, std::string_view(nullptr, 0));
    } else {
      if (fuel <= 0) {
        return std::make_pair(
            std::make_optional<std::basic_string_view<char>>(s),
            std::string_view(nullptr, 0));
      } else {
        unsigned int fuel_ = fuel - 1;
        int c = s[index];
        if (hard.contains(c)) {
          return std::make_pair(
              std::make_optional<std::basic_string_view<char>>(
                  s.substr(0, index)),
              s.substr(index + 1, input.length() - index + 1));
        } else {
          if (soft.contains(c)) {
            if (index == 0) {
              return aux(fuel_, 0, s.substr(1, input.length() - 1));
            } else {
              return std::make_pair(
                  std::make_optional<std::basic_string_view<char>>(
                      s.substr(0, index)),
                  s.substr(index + 1, input.length() - index + 1));
            }
          } else {
            return aux(fuel_, index + 1, s);
          }
        }
      }
    }
  };
  return aux(static_cast<unsigned int>(input.length()), 0, input);
}

std::shared_ptr<List::list<std::basic_string_view<char>>>
Tokenizer::list_tokens(const std::basic_string_view<char> input,
                       const std::basic_string_view<char> soft,
                       const std::basic_string_view<char> hard) {
  std::function<std::shared_ptr<List::list<std::basic_string_view<char>>>(
      unsigned int, std::basic_string_view<char>)>
      aux;
  aux = [&](unsigned int fuel, std::basic_string_view<char> rest)
      -> std::shared_ptr<List::list<std::basic_string_view<char>>> {
    if (fuel <= 0) {
      return List::list<std::basic_string_view<char>>::ctor::nil_();
    } else {
      unsigned int fuel_ = fuel - 1;
      std::pair<std::optional<std::basic_string_view<char>>,
                std::basic_string_view<char>>
          t = next_token(rest, soft, hard);
      if (t.first.has_value()) {
        std::basic_string_view<char> t_ = *t.first;
        return List::list<std::basic_string_view<char>>::ctor::cons_(
            t_, aux(fuel_, t.second));
      } else {
        return List::list<std::basic_string_view<char>>::ctor::nil_();
      }
    }
  };
  return aux(static_cast<unsigned int>(input.length()), input);
}
