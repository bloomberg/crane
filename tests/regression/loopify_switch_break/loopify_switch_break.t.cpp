// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.

// Regression test: loopified switch statements must emit break after each case.
// Without break, case fallthrough produces wrong results.

#include <iostream>
#include <loopify_switch_break.h>

namespace {
int testStatus = 0;
void aSsErT(bool condition, const char *message, int line) {
  if (condition) {
    std::cout << "Error " __FILE__ "(" << line << "): " << message
              << "    (failed)" << std::endl;
    if (0 <= testStatus && testStatus <= 100)
      ++testStatus;
  }
}
} // namespace
#define ASSERT(X) aSsErT(!(X), #X, __LINE__);

int main() {
  using Tag = LoopifySwitchBreak::Tag;
  using TagList = ::List<std::pair<Tag, uint64_t>>;

  // eval_ops: Add 10, Mul 3, Keep 0, Add 5
  // Starting from acc=0: 0+10=10, 10*3=30, 30, 30+5=35
  auto ops = TagList::cons(
      {Tag::ADD, 10u},
      TagList::cons(
          {Tag::MUL, 3u},
          TagList::cons(
              {Tag::KEEP, 0u},
              TagList::cons(
                  {Tag::ADD, 5u},
                  TagList::nil()))));

  auto result = LoopifySwitchBreak::eval_ops(ops, 0u);
  ASSERT(result == 35u);

  // eval_ops: single Mul
  auto ops2 = TagList::cons({Tag::MUL, 7u}, TagList::nil());
  ASSERT(LoopifySwitchBreak::eval_ops(ops2, 3u) == 21u);

  // eval_ops: single Add
  auto ops3 = TagList::cons({Tag::ADD, 4u}, TagList::nil());
  ASSERT(LoopifySwitchBreak::eval_ops(ops3, 1u) == 5u);

  // eval_ops: single Keep
  auto ops4 = TagList::cons({Tag::KEEP, 99u}, TagList::nil());
  ASSERT(LoopifySwitchBreak::eval_ops(ops4, 42u) == 42u);

  // eval_ops: empty
  ASSERT(LoopifySwitchBreak::eval_ops(TagList::nil(), 7u) == 7u);

  // collect_ops: Add 10, Mul 3 starting from 0
  // Expect: [0, 10, 30]
  auto ops5 = TagList::cons(
      {Tag::ADD, 10u},
      TagList::cons(
          {Tag::MUL, 3u},
          TagList::nil()));
  auto collected = LoopifySwitchBreak::collect_ops(ops5, 0u);
  ASSERT(std::holds_alternative<::List<uint64_t>::Cons>(collected.v()));
  {
    const auto &[a0, a1] = std::get<::List<uint64_t>::Cons>(collected.v());
    ASSERT(a0 == 0u);
    ASSERT(std::holds_alternative<::List<uint64_t>::Cons>(a1->v()));
    const auto &[b0, b1] = std::get<::List<uint64_t>::Cons>(a1->v());
    ASSERT(b0 == 10u);
    ASSERT(std::holds_alternative<::List<uint64_t>::Cons>(b1->v()));
    const auto &[c0, c1] = std::get<::List<uint64_t>::Cons>(b1->v());
    ASSERT(c0 == 30u);
    ASSERT(std::holds_alternative<::List<uint64_t>::Nil>(c1->v()));
  }

  // count_tag: count Add in [Add 1, Mul 2, Add 3, Keep 4, Add 5]
  auto ops6 = TagList::cons(
      {Tag::ADD, 1u},
      TagList::cons(
          {Tag::MUL, 2u},
          TagList::cons(
              {Tag::ADD, 3u},
              TagList::cons(
                  {Tag::KEEP, 4u},
                  TagList::cons(
                      {Tag::ADD, 5u},
                      TagList::nil())))));
  ASSERT(LoopifySwitchBreak::count_tag(Tag::ADD, ops6) == 3u);
  ASSERT(LoopifySwitchBreak::count_tag(Tag::MUL, ops6) == 1u);
  ASSERT(LoopifySwitchBreak::count_tag(Tag::KEEP, ops6) == 1u);

  return testStatus;
}
