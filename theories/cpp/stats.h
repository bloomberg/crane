// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
//
// Runtime event counters for measuring generated code, compiled in only with
// CRANE_STATS defined (every translation unit alike); the totals go to stderr
// at exit.  Without it every [CRANE_STAT] is nothing.
//
//   lazy.value     nodes built around a value already computed
//   lazy.direct    values already computed held in the cell's word, no node
//   lazy.thunk     cells built around a thunk ([fn] or [delegate])
//   lazy.convert   cells built by [converted_from] around a conversion
//   lazy.roundtrip [converted_from] calls answered with the source's origin
//   lazy.force     forces of a node; lazy.force_value those that found a
//                  value at once; lazy.force_direct forces of a held value
//   lazy.link      links followed; lazy.compress links retargeted
//   lazy.adopt     forced results moved into the forcing cell
//   block.free     blocks freed; block.drain frees queued during another
//   sv.block       shared-variant blocks built
#pragma once
#ifdef CRANE_STATS
#include <cstdio>

namespace crane::stats_detail {
struct counters {
  unsigned long long lazy_value = 0, lazy_direct = 0, lazy_force_direct = 0, lazy_thunk = 0, lazy_convert = 0,
                     lazy_roundtrip = 0, lazy_force = 0, lazy_force_value = 0,
                     lazy_link = 0, lazy_compress = 0, lazy_adopt = 0,
                     block_free = 0, block_drain = 0, sv_block = 0;
  ~counters() {
    std::fprintf(stderr,
                 "crane stats: lazy.value=%llu lazy.direct=%llu lazy.force_direct=%llu "
                 "lazy.thunk=%llu lazy.convert=%llu "
                 "lazy.roundtrip=%llu lazy.force=%llu lazy.force_value=%llu "
                 "lazy.link=%llu lazy.compress=%llu lazy.adopt=%llu "
                 "block.free=%llu block.drain=%llu sv.block=%llu\n",
                 lazy_value, lazy_direct, lazy_force_direct, lazy_thunk, lazy_convert, lazy_roundtrip, lazy_force,
                 lazy_force_value, lazy_link, lazy_compress, lazy_adopt, block_free,
                 block_drain, sv_block);
  }
};
inline counters &get() noexcept {
  static counters c;
  return c;
}
} // namespace crane::stats_detail
#define CRANE_STAT(field) (++::crane::stats_detail::get().field)
#else
#define CRANE_STAT(field) ((void)0)
#endif
