#include <bake_readable_image.h>

#include <iostream>
#include <string>

using M = BakeReadableImage;

static const M::rose::Rose0 &fields(const M::rose &r) {
  return std::get<M::rose::Rose0>(r.v());
}

int main() {
  int failures = 0;
  auto check = [&](bool ok, const char *what) {
    if (!ok) {
      std::cout << "FAIL: " << what << std::endl;
      ++failures;
    }
  };
  check(M::all_labels == "abcdebc", "labels");
  check(M::blue_count == 3, "blue count");
  std::string expected[] = {"say \"hi\"", "back\\slash", std::string("\x01" "a"),
                            std::string(2, '\0')};
  int i = 0;
  for (const auto &s : M::odd_strings) check(i < 4 && s == expected[i++], "odd string");
  check(i == 4, "odd string count");
  check(M::numbers.first == -42 && M::numbers.second == -0.25, "numbers");
  // ["a"]'s children are the tail of ["d"]'s: the same cells, read back.
  const M::rose &a = M::forest.front();
  const M::rose &d = M::forest.tail().front();
  check(fields(a).shade == M::Color::RED && fields(d).shade == M::Color::BLUE,
        "shades");
  check(&fields(a).kids.front() == &fields(d).kids.tail().front(),
        "shared suffix");
  std::cout << (failures ? "bake_readable_image: failed"
                         : "bake_readable_image: ok")
            << std::endl;
  return failures ? 1 : 0;
}
