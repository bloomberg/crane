#ifndef INCLUDED_EMBED_EFFECT
#define INCLUDED_EMBED_EFFECT

#include <cstdint>
#include <embed_effect_helper.h>
#include <memory>
#include <optional>
#include <string>
#include <type_traits>
#include <variant>

void bug_create(const std::string title);

template <typename T1 = void> int64_t bug_read() { return bug_read_impl(); }

int64_t bug_main();

#endif // INCLUDED_EMBED_EFFECT
