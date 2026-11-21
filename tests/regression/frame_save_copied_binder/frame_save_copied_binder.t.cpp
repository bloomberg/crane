#include <frame_save_copied_binder.h>
#include <cassert>
#include <cstdint>
#include <vector>

using M = FrameSaveCopiedBinder;

static std::vector<uint64_t> elems(const crane::list<uint64_t> &l) {
  std::vector<uint64_t> v;
  for (auto x : l)
    v.push_back(x);
  return v;
}

static crane::list<uint64_t> of(std::vector<uint64_t> v) {
  return crane::list<uint64_t>::from_range(v.begin(), v.end());
}

int main() {
  // No memo hit: the scan recurses to the end of the input and resumes in
  // every frame.
  {
    auto [c, o] = M::scan(std::nullopt, of({1, 2, 3}), UINT64_C(3),
                          crane::list<uint64_t>{});
    assert(c == 1);
    assert(o.has_value());
    assert(elems(o->first.first) == (std::vector<uint64_t>{1, 2}));
    assert(elems(o->first.second) == (std::vector<uint64_t>{3}));
    assert(o->second == 1);
  }
  // A memo hit at the second element stops the recursion there.
  {
    auto [c, o] = M::scan(std::optional<uint64_t>(UINT64_C(2)), of({1, 2, 3}),
                          UINT64_C(3), crane::list<uint64_t>{});
    assert(c == 2);
    assert(o.has_value());
    assert(elems(o->first.first) == (std::vector<uint64_t>{1, 2}));
    assert(elems(o->first.second) == (std::vector<uint64_t>{3}));
    assert(o->second == 1);
  }
  // A deep scan: every frame resumes, reading the list it moved in.
  {
    std::vector<uint64_t> ones(100000, 1);
    crane::list<uint64_t> s = of(ones);
    auto [c, o] = M::scan(std::nullopt, s, UINT64_C(100000),
                          crane::list<uint64_t>{});
    assert(c == 100001);
    assert(!o.has_value());
    // The caller's list is untouched.
    assert(s.size() == 100000);
  }
  return 0;
}
