#include "bake_readable_image.h"

BakeReadableImage::rose BakeReadableImage::leaf(const std::string &s,
                                                BakeReadableImage::Color c) {
  return rose::rose0(s, c, crane::list<crane::box<BakeReadableImage::rose>>{});
}

std::string BakeReadableImage::labels(const BakeReadableImage::rose &r) {
  const auto &[label, _, kids] =
      std::get<typename BakeReadableImage::rose::Rose0>(r.v());
  return List::template fold_left<std::string, BakeReadableImage::rose>(
      [](const std::string &acc,
         const BakeReadableImage::rose &k) {
        return crane::string_capped(acc + labels(k));
      },
      kids, label);
}

// Baked by crane::bake: the value of crane_baked_forest_ac321626c191.
static_assert(crane::bake::data_model == 0x80408080402u,
              "crane::bake: baked on a host with other scalar widths");
constinit const char crane_baked_forest_ac321626c191_text[] = "b" "c" "a" "e"
    "d";
constinit const std::uint64_t crane_baked_forest_ac321626c191_words[] = {
    1, 1,        // crane::list<crane::box<BakeReadableImage::rose>>: #0
    0,           // #0 nil
    2, 2,        // BakeReadableImage::rose: #1 to #2
    0, 1, 1, 0,  // #1 Rose0{label = "b", shade = GREEN, kids = #0}
    0, 1, 2, 0,  // #2 Rose0{label = "c", shade = BLUE, kids = #0}
    1, 2,        // crane::list<crane::box<BakeReadableImage::rose>>: #3 to #4
    1, 2, 0,     // #3 cons{head = #2, tail = #0}
    1, 1, 3,     // #4 cons{head = #1, tail = #3}
    2, 2,        // BakeReadableImage::rose: #5 to #6
    0, 1, 0, 4,  // #5 Rose0{label = "a", shade = RED, kids = #4}
    0, 1, 0, 0,  // #6 Rose0{label = "e", shade = RED, kids = #0}
    1, 1,        // crane::list<crane::box<BakeReadableImage::rose>>: #7
    1, 6, 4,     // #7 cons{head = #6, tail = #4}
    2, 1,        // BakeReadableImage::rose: #8
    0, 1, 2, 7,  // #8 Rose0{label = "d", shade = BLUE, kids = #7}
    1, 2,        // crane::list<crane::box<BakeReadableImage::rose>>: #9 to #10
    1, 8, 0,     // #9 cons{head = #8, tail = #0}
    1, 5, 9,     // #10 cons{head = #5, tail = #9}
    0,           // end of the nodes
    10,          // the value: #10
};
constinit const crane::bake::image crane_baked_forest_ac321626c191{
    crane_baked_forest_ac321626c191_words, 52, nullptr, 0,
    crane_baked_forest_ac321626c191_text, 5};

// Baked by crane::bake: the value of crane_baked_numbers_f28e8ab85c63.
static_assert(crane::bake::data_model == 0x80408080402u,
              "crane::bake: baked on a host with other scalar widths");
constinit const std::uint64_t crane_baked_numbers_f28e8ab85c63_words[] = {
    0,  // no nodes
    // the value: {-42, -0.25}
    18446744073709551574u, 13821547256400052224u,
};
constinit const crane::bake::image crane_baked_numbers_f28e8ab85c63{
    crane_baked_numbers_f28e8ab85c63_words, 3, nullptr, 0, nullptr, 0};

// Baked by crane::bake: the value of crane_baked_odd_strings_48cd7c9a95e8.
static_assert(crane::bake::data_model == 0x80408080402u,
              "crane::bake: baked on a host with other scalar widths");
constinit const char crane_baked_odd_strings_48cd7c9a95e8_text[] = "\x00\x00"
    "\x01" "a" "back\\slash" "say \"hi\"";
constinit const std::uint64_t crane_baked_odd_strings_48cd7c9a95e8_words[] = {
    1, 5,      // crane::list<std::string>: #0 to #4
    0,         // #0 nil
    1, 2, 0,   // #1 cons{head = "\x00\x00", tail = #0}
    1, 2, 1,   // #2 cons{head = "\x01" "a", tail = #1}
    1, 10, 2,  // #3 cons{head = "back\\slash", tail = #2}
    1, 8, 3,   // #4 cons{head = "say \"hi\"", tail = #3}
    0,         // end of the nodes
    4,         // the value: #4
};
constinit const crane::bake::image crane_baked_odd_strings_48cd7c9a95e8{
    crane_baked_odd_strings_48cd7c9a95e8_words, 17, nullptr, 0,
    crane_baked_odd_strings_48cd7c9a95e8_text, 22};
