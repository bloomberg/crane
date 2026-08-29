#include "custom_inline_bug.h"

std::optional<uint64_t>
CustomInlineBug::bug_some_proj(const CustomInlineBug::State &s) {
  return std::make_optional<uint64_t>(s.value);
}

std::pair<CustomInlineBug::State, uint64_t>
CustomInlineBug::bug_pair_proj(CustomInlineBug::State s) {
  return std::make_pair(s, s.value);
}

std::optional<std::optional<uint64_t>>
CustomInlineBug::bug_nested_option(const CustomInlineBug::State &s) {
  return std::make_optional<std::optional<uint64_t>>(
      std::make_optional<uint64_t>(s.value));
}

std::optional<std::pair<CustomInlineBug::State, uint64_t>>
CustomInlineBug::bug_option_pair(CustomInlineBug::State s) {
  return std::make_optional<std::pair<CustomInlineBug::State, uint64_t>>(
      std::make_pair(s, s.value));
}

CustomInlineBug::State CustomInlineBug::get_state(uint64_t n) {
  return State{n, n};
}

std::optional<uint64_t> CustomInlineBug::bug_some_of_call(uint64_t n) {
  return std::make_optional<uint64_t>(get_state(n).value);
}

std::pair<CustomInlineBug::State, uint64_t>
CustomInlineBug::pair_simple(CustomInlineBug::State s) {
  return std::make_pair(s, s.value);
}

std::pair<CustomInlineBug::State, uint64_t>
CustomInlineBug::pair_let(uint64_t n) {
  CustomInlineBug::State s = State{n, n};
  return std::make_pair(s, s.value);
}

std::pair<std::pair<CustomInlineBug::State, uint64_t>,
          std::pair<uint64_t, uint64_t>>
CustomInlineBug::pair_nested(CustomInlineBug::State s) {
  return std::make_pair(std::make_pair(s, s.value),
                        std::make_pair(s.value, s.data));
}

std::pair<CustomInlineBug::State, uint64_t>
CustomInlineBug::pair_if(bool b, CustomInlineBug::State s) {
  if (b) {
    return std::make_pair(s, s.value);
  } else {
    return std::make_pair(std::move(s), UINT64_C(0));
  }
}

std::optional<std::pair<CustomInlineBug::State, uint64_t>>
CustomInlineBug::pair_match(const std::optional<CustomInlineBug::State> &o) {
  if (o.has_value()) {
    const CustomInlineBug::State &s = *o;
    return std::make_optional<std::pair<CustomInlineBug::State, uint64_t>>(
        std::make_pair(s, s.value));
  } else {
    return std::optional<std::pair<CustomInlineBug::State, uint64_t>>();
  }
}

std::pair<std::pair<CustomInlineBug::State, uint64_t>, uint64_t>
CustomInlineBug::pair_multi_proj(CustomInlineBug::State s) {
  return std::make_pair(std::make_pair(s, s.value), s.data);
}

std::pair<CustomInlineBug::State, uint64_t>
CustomInlineBug::pair_chain(const CustomInlineBug::State &s1) {
  CustomInlineBug::State s2 = State{s1.value, s1.data};
  CustomInlineBug::State s3 = State{s2.value, s2.data};
  return std::make_pair(s3, s3.value);
}

std::pair<std::pair<CustomInlineBug::State, CustomInlineBug::State>,
          std::pair<uint64_t, uint64_t>>
CustomInlineBug::pair_extreme(CustomInlineBug::State s) {
  return std::make_pair(std::make_pair(s, s), std::make_pair(s.value, s.data));
}

std::pair<CustomInlineBug::State, uint64_t>
CustomInlineBug::make_pair(CustomInlineBug::State s) {
  return std::make_pair(s, s.value);
}

std::pair<CustomInlineBug::State, uint64_t>
CustomInlineBug::outer_pair(uint64_t n) {
  return make_pair(State{n, n});
}

List<std::pair<CustomInlineBug::State, uint64_t>>
CustomInlineBug::count_pairs(uint64_t n, CustomInlineBug::State s) {
  if (n <= 0) {
    return List<std::pair<CustomInlineBug::State, uint64_t>>::nil();
  } else {
    uint64_t m = n - 1;
    return List<std::pair<CustomInlineBug::State, uint64_t>>::cons(
        std::make_pair(s, s.value), count_pairs(m, s));
  }
}
