#include <custom_inline_bug.h>

__attribute__((pure)) std::optional<unsigned int>
CustomInlineBug::bug_some_proj(const CustomInlineBug::State &s) {
  return std::make_optional<unsigned int>(s.value);
}

__attribute__((pure)) std::pair<CustomInlineBug::State, unsigned int>
CustomInlineBug::bug_pair_proj(CustomInlineBug::State s) {
  return std::make_pair(s, s.value);
}

__attribute__((pure)) std::optional<std::optional<unsigned int>>
CustomInlineBug::bug_nested_option(const CustomInlineBug::State &s) {
  return std::make_optional<std::optional<unsigned int>>(
      std::make_optional<unsigned int>(s.value));
}

__attribute__((pure))
std::optional<std::pair<CustomInlineBug::State, unsigned int>>
CustomInlineBug::bug_option_pair(CustomInlineBug::State s) {
  return std::make_optional<std::pair<CustomInlineBug::State, unsigned int>>(
      std::make_pair(s, s.value));
}

__attribute__((pure)) CustomInlineBug::State
CustomInlineBug::get_state(unsigned int n) {
  return State{n, n};
}

__attribute__((pure)) std::optional<unsigned int>
CustomInlineBug::bug_some_of_call(const unsigned int &n) {
  return std::make_optional<unsigned int>(get_state(n).value);
}

__attribute__((pure)) std::pair<CustomInlineBug::State, unsigned int>
CustomInlineBug::pair_simple(CustomInlineBug::State s) {
  return std::make_pair(s, s.value);
}

__attribute__((pure)) std::pair<CustomInlineBug::State, unsigned int>
CustomInlineBug::pair_let(unsigned int n) {
  CustomInlineBug::State s = State{n, n};
  return std::make_pair(s, s.value);
}

__attribute__((pure)) std::pair<std::pair<CustomInlineBug::State, unsigned int>,
                                std::pair<unsigned int, unsigned int>>
CustomInlineBug::pair_nested(CustomInlineBug::State s) {
  return std::make_pair(std::make_pair(s, s.value),
                        std::make_pair(s.value, s.data));
}

__attribute__((pure)) std::pair<CustomInlineBug::State, unsigned int>
CustomInlineBug::pair_if(const bool &b, CustomInlineBug::State s) {
  if (b) {
    return std::make_pair(s, s.value);
  } else {
    return std::make_pair(std::move(s), 0u);
  }
}

__attribute__((pure))
std::optional<std::pair<CustomInlineBug::State, unsigned int>>
CustomInlineBug::pair_match(const std::optional<CustomInlineBug::State> &o) {
  if (o.has_value()) {
    const CustomInlineBug::State &s = *o;
    return std::make_optional<std::pair<CustomInlineBug::State, unsigned int>>(
        std::make_pair(s, s.value));
  } else {
    return std::optional<std::pair<CustomInlineBug::State, unsigned int>>();
  }
}

__attribute__((pure))
std::pair<std::pair<CustomInlineBug::State, unsigned int>, unsigned int>
CustomInlineBug::pair_multi_proj(CustomInlineBug::State s) {
  return std::make_pair(std::make_pair(s, s.value), s.data);
}

__attribute__((pure)) std::pair<CustomInlineBug::State, unsigned int>
CustomInlineBug::pair_chain(const CustomInlineBug::State &s1) {
  CustomInlineBug::State s2 = State{s1.value, s1.data};
  CustomInlineBug::State s3 = State{s2.value, s2.data};
  return std::make_pair(s3, s3.value);
}

__attribute__((pure))
std::pair<std::pair<CustomInlineBug::State, CustomInlineBug::State>,
          std::pair<unsigned int, unsigned int>>
CustomInlineBug::pair_extreme(CustomInlineBug::State s) {
  return std::make_pair(std::make_pair(s, s), std::make_pair(s.value, s.data));
}

__attribute__((pure)) std::pair<CustomInlineBug::State, unsigned int>
CustomInlineBug::make_pair(CustomInlineBug::State s) {
  return std::make_pair(s, s.value);
}

__attribute__((pure)) std::pair<CustomInlineBug::State, unsigned int>
CustomInlineBug::outer_pair(unsigned int n) {
  return make_pair(State{n, n});
}

__attribute__((pure)) List<std::pair<CustomInlineBug::State, unsigned int>>
CustomInlineBug::count_pairs(const unsigned int &n, CustomInlineBug::State s) {
  if (n <= 0) {
    return List<std::pair<CustomInlineBug::State, unsigned int>>::nil();
  } else {
    unsigned int m = n - 1;
    return List<std::pair<CustomInlineBug::State, unsigned int>>::cons(
        std::make_pair(s, s.value), count_pairs(m, s));
  }
}
