// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <tokenizer.h>

#include <cstring>
#include <functional>
#include <iostream>
#include <memory>
#include <string>
#include <string_view>
#include <variant>

// ============================================================================
//                     STANDARD BDE ASSERT TEST FUNCTION
// ----------------------------------------------------------------------------

namespace {

int testStatus = 0;

void aSsErT(bool condition, const char *message, int line) {
  if (condition) {
    std::cout << "Error " __FILE__ "(" << line << "): " << message
              << "    (failed)" << std::endl;

    if (0 <= testStatus && testStatus <= 100) {
      ++testStatus;
    }
  }
}

} // namespace

#define ASSERT(X) aSsErT(!(X), #X, __LINE__);

std::string s_of_sv(std::basic_string_view<char> sv) {
  std::string s(sv);
  return s;
}

std::vector<std::string> tokenize_functional(const std::string soft,
                                             std::string input) {
  std::basic_string_view<char> delim = {soft.data(), soft.size()};
  std::basic_string_view<char> in = {input.data(), input.size()};
  auto l = list_tokens(in, delim, std::string_view(nullptr, 0));
  return list_to_vec_map<std::basic_string_view<char>, std::string>(s_of_sv, l);
}

std::vector<std::string> tokenize_cpp(const std::string soft,
                                      std::string input) {
  auto delim = soft.c_str();
  auto tok = std::strtok(input.data(), delim);
  std::vector<std::string> v = {};
  while (tok) {
    std::string s(tok);
    v.push_back(s);
    tok = std::strtok(nullptr, delim);
  }
  return v;
}

extern "C" int LLVMFuzzerTestOneInput(const uint8_t *Data, size_t Size) {
  // Need at least 2 bytes to split: one for choosing a soft length, one for
  // payload.
  if (Size < 2)
    return 0;

  // Use the first byte to choose the delimiter length within bounds.
  size_t soft_len = static_cast<size_t>(Data[0]) % (Size / 2); // 0 .. Size/2
  const char *p = reinterpret_cast<const char *>(Data + 1);

  std::string soft_raw(p, p + soft_len);
  std::string input_raw(p + soft_len, p + (Size - 1));

  // Sanitize NULs because strtok treats '\0' as terminator; also avoid UB if
  // soft is empty.
  auto sanitize_no_nul = [](std::string &s) {
    for (auto &ch : s) {
      if (ch == '\0')
        ch = 'x'; // any non-zero byte is fine
    }
  };
  sanitize_no_nul(soft_raw);
  sanitize_no_nul(input_raw);

  if (soft_raw.empty())
    return 0; // strtok with empty delimiters is undefined

  // std::cout << soft_raw + " " + input_raw + "\n";

  // Run both tokenizers.
  std::vector<std::string> t_func = tokenize_functional(soft_raw, input_raw);
  // tokenize_cpp mutates its input; pass a copy.
  std::vector<std::string> t_cpp =
      tokenize_cpp(soft_raw, std::string(input_raw));

  // Compare results exactly; if they differ, crash to report the input.
  if (t_func.size() != t_cpp.size()) {
    abort();
  }
  for (size_t i = 0; i < t_func.size(); ++i) {
    if (t_func[i] != t_cpp[i]) {
      abort();
    }
  }

  return 0;
}

// clang++ -I. -std=c++23 -O1 -g -fsanitize=fuzzer,address tokenizer.cpp
// tokenizer.d.cpp -o tokenizer.d.o; ./tokenizer.d.o
// -artifact_prefix=./artifacts/ corpus/
