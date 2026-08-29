#ifndef INCLUDED_EMBED_EFFECT
#define INCLUDED_EMBED_EFFECT

#include <cstdint>
#include <embed_effect_helper.h>
#include <string>
#include <utility>
#include <variant>

void bug_create(std::string title);

template <typename T1 = void> int64_t bug_read() { return bug_read_impl(); }

int64_t bug_main();

#endif // INCLUDED_EMBED_EFFECT
