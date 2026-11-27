#pragma once

#include <cstdint>
#include <embed_effect_helper.h>
#include <string>
#include <string_view>
#include <variant>

void bug_create(const std::string &title);
int64_t bug_read();
int64_t bug_main();
