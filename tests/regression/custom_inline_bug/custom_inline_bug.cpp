#include <custom_inline_bug.h>

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) std::optional<unsigned int>
CustomInlineBug::bug_some_proj(
    const std::shared_ptr<CustomInlineBug::State> &s) {
  return std::make_optional<unsigned int>(s->value);
}

__attribute__((pure))
std::pair<std::shared_ptr<CustomInlineBug::State>, unsigned int>
CustomInlineBug::bug_pair_proj(std::shared_ptr<CustomInlineBug::State> s) {
  return std::make_pair(s, s->value);
}

__attribute__((pure)) std::optional<std::optional<unsigned int>>
CustomInlineBug::bug_nested_option(
    const std::shared_ptr<CustomInlineBug::State> &s) {
  return std::make_optional<std::optional<unsigned int>>(
      std::make_optional<unsigned int>(s->value));
}

__attribute__((pure))
std::optional<std::pair<std::shared_ptr<CustomInlineBug::State>, unsigned int>>
CustomInlineBug::bug_option_pair(std::shared_ptr<CustomInlineBug::State> s) {
  return std::make_optional<
      std::pair<std::shared_ptr<CustomInlineBug::State>, unsigned int>>(
      std::make_pair(s, s->value));
}

std::shared_ptr<CustomInlineBug::State>
CustomInlineBug::get_state(const unsigned int n) {
  return std::make_shared<CustomInlineBug::State>(State{n, n});
}

__attribute__((pure)) std::optional<unsigned int>
CustomInlineBug::bug_some_of_call(const unsigned int n) {
  return std::make_optional<unsigned int>(get_state(n)->value);
}

__attribute__((pure))
std::pair<std::shared_ptr<CustomInlineBug::State>, unsigned int>
CustomInlineBug::pair_simple(std::shared_ptr<CustomInlineBug::State> s) {
  return std::make_pair(s, s->value);
}

__attribute__((pure))
std::pair<std::shared_ptr<CustomInlineBug::State>, unsigned int>
CustomInlineBug::pair_let(const unsigned int n) {
  std::shared_ptr<CustomInlineBug::State> s =
      std::make_shared<CustomInlineBug::State>(State{n, n});
  return std::make_pair(s, s->value);
}

__attribute__((pure))
std::pair<std::pair<std::shared_ptr<CustomInlineBug::State>, unsigned int>,
          std::pair<unsigned int, unsigned int>>
CustomInlineBug::pair_nested(std::shared_ptr<CustomInlineBug::State> s) {
  return std::make_pair(std::make_pair(s, s->value),
                        std::make_pair(s->value, s->data));
}

__attribute__((pure))
std::pair<std::shared_ptr<CustomInlineBug::State>, unsigned int>
CustomInlineBug::pair_if(const bool b,
                         std::shared_ptr<CustomInlineBug::State> s) {
  if (b) {
    return std::make_pair(s, s->value);
  } else {
    return std::make_pair(s, 0u);
  }
}

__attribute__((pure))
std::optional<std::pair<std::shared_ptr<CustomInlineBug::State>, unsigned int>>
CustomInlineBug::pair_match(
    const std::optional<std::shared_ptr<CustomInlineBug::State>> o) {
  if (o.has_value()) {
    std::shared_ptr<CustomInlineBug::State> s = *o;
    return std::make_optional<
        std::pair<std::shared_ptr<CustomInlineBug::State>, unsigned int>>(
        std::make_pair(s, s->value));
  } else {
    return std::optional<
        std::pair<std::shared_ptr<CustomInlineBug::State>, unsigned int>>();
  }
}

__attribute__((pure))
std::pair<std::pair<std::shared_ptr<CustomInlineBug::State>, unsigned int>,
          unsigned int>
CustomInlineBug::pair_multi_proj(std::shared_ptr<CustomInlineBug::State> s) {
  return std::make_pair(std::make_pair(s, s->value), s->data);
}

__attribute__((pure))
std::pair<std::shared_ptr<CustomInlineBug::State>, unsigned int>
CustomInlineBug::pair_chain(const std::shared_ptr<CustomInlineBug::State> &s1) {
  std::shared_ptr<CustomInlineBug::State> s2 =
      std::make_shared<CustomInlineBug::State>(State{s1->value, s1->data});
  std::shared_ptr<CustomInlineBug::State> s3 =
      std::make_shared<CustomInlineBug::State>(State{s2->value, s2->data});
  return std::make_pair(s3, s3->value);
}

__attribute__((pure))
std::pair<std::pair<std::shared_ptr<CustomInlineBug::State>,
                    std::shared_ptr<CustomInlineBug::State>>,
          std::pair<unsigned int, unsigned int>>
CustomInlineBug::pair_extreme(std::shared_ptr<CustomInlineBug::State> s) {
  return std::make_pair(std::make_pair(s, s),
                        std::make_pair(s->value, s->data));
}

__attribute__((pure))
std::pair<std::shared_ptr<CustomInlineBug::State>, unsigned int>
CustomInlineBug::make_pair(std::shared_ptr<CustomInlineBug::State> s) {
  return std::make_pair(s, s->value);
}

__attribute__((pure))
std::pair<std::shared_ptr<CustomInlineBug::State>, unsigned int>
CustomInlineBug::outer_pair(const unsigned int n) {
  return make_pair(std::make_shared<CustomInlineBug::State>(State{n, n}));
}

std::shared_ptr<
    List<std::pair<std::shared_ptr<CustomInlineBug::State>, unsigned int>>>
CustomInlineBug::count_pairs(const unsigned int n,
                             std::shared_ptr<CustomInlineBug::State> s) {
  if (n <= 0) {
    return List<std::pair<std::shared_ptr<CustomInlineBug::State>,
                          unsigned int>>::nil();
  } else {
    unsigned int m = n - 1;
    return List<std::pair<std::shared_ptr<CustomInlineBug::State>,
                          unsigned int>>::cons(std::make_pair(s, s->value),
                                               count_pairs(m, s));
  }
}
