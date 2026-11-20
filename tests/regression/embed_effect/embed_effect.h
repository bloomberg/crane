#pragma once

#include <cstdint>
#include <embed_effect_helper.h>
#include <string>
#include <string_view>
#include <variant>

template <typename T1 = void> void bug_create(const std::string &title);

template <typename T1 = void> int64_t bug_read() { return bug_read_impl(); }

int64_t bug_main();
