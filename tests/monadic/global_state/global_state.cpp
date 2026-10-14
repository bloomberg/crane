#include "global_state.h"

uint64_t
GlobalStateTests::fib_fun(uint64_t n) { /// CraneEnter: captures varying
                                        /// parameters for each recursive call.

  struct CraneEnter {
    uint64_t n;
  };

  /// CraneCont_m: saves [m], resumes after recursive call, then processes rest.
  struct CraneCont_m {
    uint64_t m;
  };

  /// CraneCont_m_1: saves [_tmp2], resumes after recursive call, then processes
  /// rest.
  struct CraneCont_m_1 {
    uint64_t _tmp2;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_m, CraneCont_m_1>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{n});
  /// Loopified fib_fun: CraneEnter -> CraneCont_m -> CraneCont_m_1.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      uint64_t n = _f.n;
      if (n <= 0) {
        _result = UINT64_C(0);
      } else {
        uint64_t m0 = n - 1;
        if (m0 <= 0) {
          _result = UINT64_C(1);
        } else {
          uint64_t m = m0 - 1;
          _stack.emplace_back(CraneCont_m{m});
          _stack.emplace_back(CraneEnter{m0});
        }
      }
    } else if (std::holds_alternative<CraneCont_m>(_frame)) {
      auto _f = std::move(std::get<CraneCont_m>(_frame));
      uint64_t m = _f.m;
      _stack.emplace_back(CraneCont_m_1{std::move(_result)});
      _stack.emplace_back(CraneEnter{m});
    } else {
      auto _f = std::move(std::get<CraneCont_m_1>(_frame));
      _result = (_f._tmp2 + std::move(_result));
    }
  }
  return _result;
}

uint64_t GlobalStateTests::counter() {
  auto &&_once1 =
      GlobalStateExamples::template ctr_idx<GlobalStateTests::nat_idx,
                                            uint64_t>();
  return (_crane_globals[_once1] = UINT64_C(0), _once1);
}

uint64_t GlobalStateTests::counter_next_mine(uint64_t ctr) {
  uint64_t a = crane::any_cast<uint64_t>(_crane_globals.at(ctr));
  _crane_globals[std::move(ctr)] = (a + UINT64_C(1));
  return a;
}

std::string GlobalStateTests::gensym(uint64_t counter0, std::string prefix) {
  uint64_t v = counter_next_mine(std::move(counter0));
  return std::move(prefix) + std::to_string(v);
}

List<uint64_t> ListDef::seq(uint64_t start, uint64_t len) {
  std::optional<List<uint64_t>> _root{};
  std::shared_ptr<List<uint64_t>> *_write = nullptr;
  uint64_t _loop_len = len;
  uint64_t _loop_start = start;
  while (true) {
    if (_loop_len <= 0) {
      auto _value = List<uint64_t>::nil();
      (_write ? *(*_write = std::make_shared<List<uint64_t>>(std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      uint64_t len0 = _loop_len - 1;
      auto _cell = typename List<uint64_t>::Cons(_loop_start, nullptr);
      List<uint64_t> &_node =
          (_write
               ? *(*_write = std::make_shared<List<uint64_t>>(std::move(_cell)))
               : _root.emplace(std::move(_cell)));
      _write = &std::get<typename List<uint64_t>::Cons>(_node.v_mut()).l;
      _loop_len = len0;
      _loop_start = (_loop_start + 1);
      continue;
    }
  }
  return std::move(*_root);
}
