#include "frame_save_copied_binder.h"

/// A memoised longest-prefix scan shaped like ParseALot's max_pref_fn_M,
/// over a list mapped to a cons list whose match template binds the tail as
/// a variable of its own (auto %b1a1 = %scrut.tail()) and the head by
/// reference.  The tail is a copy, not a part of the scrutinee: the call
/// entering the machine takes it by move.  The frame saved across the call
/// copies the head, a part of the list, before moving the list in after it,
/// instead of copying the list.
bool FrameSaveCopiedBinder::accepting(const crane::list<uint64_t> &st) {
  if (st.empty()) {
    return false;
  } else {
    const uint64_t &x = st.front();
    auto _x = st.tail();
    return Nat::even(x);
  }
}

crane::list<uint64_t>
FrameSaveCopiedBinder::step(uint64_t a, const crane::list<uint64_t> &st) {
  return crane::cons(a, st);
}

std::optional<std::optional<std::pair<
    std::pair<crane::list<uint64_t>, crane::list<uint64_t>>, uint64_t>>>
FrameSaveCopiedBinder::lookup(std::optional<uint64_t> m, uint64_t a) {
  if (m.has_value()) {
    const uint64_t &k = *m;
    if (k == a) {
      return std::make_optional<std::optional<std::pair<
          std::pair<crane::list<uint64_t>, crane::list<uint64_t>>, uint64_t>>>(
          std::optional<
              std::pair<std::pair<crane::list<uint64_t>, crane::list<uint64_t>>,
                        uint64_t>>());
    } else {
      return std::optional<std::optional<std::pair<
          std::pair<crane::list<uint64_t>, crane::list<uint64_t>>,
          uint64_t>>>();
    }
  } else {
    return std::optional<std::optional<std::pair<
        std::pair<crane::list<uint64_t>, crane::list<uint64_t>>, uint64_t>>>();
  }
}

std::pair<uint64_t, std::optional<std::pair<
                        std::pair<crane::list<uint64_t>, crane::list<uint64_t>>,
                        uint64_t>>>
FrameSaveCopiedBinder::scan(std::optional<uint64_t> m,
                            const crane::list<uint64_t> &s, uint64_t i,
                            const crane::list<uint64_t> &st) {
  // Explicit stack replaces the non-tail recursion of scan: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    crane::list<uint64_t> st;
    uint64_t i;
    crane::list<uint64_t> s;
  };

  struct _after_scan_in_None {
    uint64_t i;
    uint64_t a;
    crane::list<uint64_t> s_;
    crane::list<uint64_t> st_;
    crane::list<uint64_t> s;
    crane::list<uint64_t> st;
  };

  using _frame = std::variant<_call, _after_scan_in_None>;
  std::pair<
      uint64_t,
      std::optional<std::pair<
          std::pair<crane::list<uint64_t>, crane::list<uint64_t>>,
          uint64_t>>> _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{st, i, s});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      crane::list<uint64_t> st = std::move(_f.st);
      uint64_t i = _f.i;
      crane::list<uint64_t> s = std::move(_f.s);
      if (s.empty()) {
        if (accepting(std::move(st))) {
          _result = std::make_pair(
              UINT64_C(0),
              std::make_optional<std::pair<
                  std::pair<crane::list<uint64_t>, crane::list<uint64_t>>,
                  uint64_t>>(std::make_pair(std::make_pair(
                  crane::list<uint64_t>{}, crane::list<uint64_t>{}),
                                            i)));
        } else {
          _result = std::make_pair(
              UINT64_C(1), std::optional<std::pair<std::pair<
                               crane::list<uint64_t>, crane::list<uint64_t>>,
                                                   uint64_t>>());
        }
      } else {
        const uint64_t &a = s.front();
        auto s_ = s.tail();
        crane::list<uint64_t> st_ = step(a, st);
        std::pair<uint64_t, std::optional<std::pair<std::pair<
                                crane::list<uint64_t>, crane::list<uint64_t>>,
                                                    uint64_t>>> mp;
        auto _cs = lookup(m, a);
        if (_cs.has_value()) {
          const std::optional<
              std::pair<std::pair<crane::list<uint64_t>, crane::list<uint64_t>>,
                        uint64_t>> &o = *_cs;
          mp = std::make_pair(UINT64_C(2), o);
          {
            auto [c, o] = std::move(mp);
            if (o.has_value()) {
              const std::pair<
                  std::pair<crane::list<uint64_t>, crane::list<uint64_t>>,
                  uint64_t> &p0 = *o;
              const auto &[p1, qi] = p0;
              const auto &[p, q] = p1;
              _result =
                  std::make_pair(
                      c, std::make_optional<std::pair<std::pair<
                             crane::list<uint64_t>, crane::list<uint64_t>>,
                                                      uint64_t>>(std::make_pair(
                             std::make_pair(crane::cons(a, p), q), qi)));
            } else {
              if (accepting(std::move(st_))) {
                _result = std::make_pair(
                    c,
                    std::make_optional<std::pair<
                        std::pair<crane::list<uint64_t>, crane::list<uint64_t>>,
                        uint64_t>>(std::make_pair(std::make_pair(
                        crane::cons(a, crane::list<uint64_t>{}), std::move(s_)),
                                                  (i ? i - 1 : i))));
              } else {
                if (accepting(std::move(st))) {
                  _result = std::make_pair(
                      c,
                      std::make_optional<std::pair<std::pair<
                          crane::list<uint64_t>, crane::list<uint64_t>>,
                                                   uint64_t>>(std::make_pair(
                          std::make_pair(crane::list<uint64_t>{}, std::move(s)),
                          i)));
                } else {
                  _result = std::make_pair((c + 1),
                                           std::optional<std::pair<
                                               std::pair<crane::list<uint64_t>,
                                                         crane::list<uint64_t>>,
                                               uint64_t>>());
                }
              }
            }
          }
        } else {
          _stack.emplace_back(
              _after_scan_in_None{i, a, s_, st_, std::move(s), std::move(st)});
          _stack.emplace_back(
              _call{std::move(st_), (i ? i - 1 : i), std::move(s_)});
        }
      }
    } else {
      auto _f = std::move(std::get<_after_scan_in_None>(_popped));
      _stack.pop_back();
      uint64_t i = _f.i;
      uint64_t a = _f.a;
      crane::list<uint64_t> s_ = std::move(_f.s_);
      crane::list<uint64_t> st_ = std::move(_f.st_);
      crane::list<uint64_t> s = std::move(_f.s);
      crane::list<uint64_t> st = std::move(_f.st);
      auto mp = std::move(_result);
      auto [c, o] = std::move(mp);
      if (o.has_value()) {
        const std::pair<std::pair<crane::list<uint64_t>, crane::list<uint64_t>>,
                        uint64_t> &p0 = *o;
        const auto &[p1, qi] = p0;
        const auto &[p, q] = p1;
        _result = std::make_pair(
            c, std::make_optional<std::pair<
                   std::pair<crane::list<uint64_t>, crane::list<uint64_t>>,
                   uint64_t>>(
                   std::make_pair(std::make_pair(crane::cons(a, p), q), qi)));
      } else {
        if (accepting(std::move(st_))) {
          _result = std::make_pair(
              c, std::make_optional<std::pair<
                     std::pair<crane::list<uint64_t>, crane::list<uint64_t>>,
                     uint64_t>>(std::make_pair(std::make_pair(
                     crane::cons(a, crane::list<uint64_t>{}), std::move(s_)),
                                               (i ? i - 1 : i))));
        } else {
          if (accepting(std::move(st))) {
            _result = std::make_pair(
                c,
                std::make_optional<std::pair<
                    std::pair<crane::list<uint64_t>, crane::list<uint64_t>>,
                    uint64_t>>(std::make_pair(
                    std::make_pair(crane::list<uint64_t>{}, std::move(s)), i)));
          } else {
            _result = std::make_pair(
                (c + 1), std::optional<std::pair<std::pair<
                             crane::list<uint64_t>, crane::list<uint64_t>>,
                                                 uint64_t>>());
          }
        }
      }
    }
  }
  return _result;
}

bool Nat::even(uint64_t n) {
  // Loop replaces the tail recursion: each recursive call updates the loop
  // variables.
  uint64_t _loop_n = n;
  while (true) {
    if (_loop_n <= 0) {
      return true;
    } else {
      uint64_t n0 = _loop_n - 1;
      if (n0 <= 0) {
        return false;
      } else {
        uint64_t n_ = n0 - 1;
        _loop_n = n_;
      }
    }
  }
}
