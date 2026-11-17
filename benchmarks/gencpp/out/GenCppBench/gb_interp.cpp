#include "gb_interp.h"

uint64_t GbInterp::next(uint64_t s) {
  auto &&_once1 = ((s * UINT64_C(75)) + UINT64_C(74));
  auto &&_once2 = UINT64_C(65537);
  return (_once2 ? _once1 % _once2 : _once1);
}

List<uint64_t> GbInterp::randoms(uint64_t n, uint64_t s) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
  std::optional<List<uint64_t>> _root{};
  std::shared_ptr<List<uint64_t>> *_write = nullptr;
  uint64_t _loop_s = s;
  uint64_t _loop_n = n;
  while (true) {
    if (_loop_n <= 0) {
      auto _value = List<uint64_t>::nil();
      (_write ? *(*_write = std::make_shared<List<uint64_t>>(std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      uint64_t n_ = _loop_n - 1;
      auto _cell = typename List<uint64_t>::Cons(_loop_s, nullptr);
      List<uint64_t> &_node =
          (_write ? *(*_write =
                          std::make_shared<List<uint64_t>>(std::move(_cell)))
                  : _root.emplace(std::move(_cell)));
      _write = &std::get<typename List<uint64_t>::Cons>(_node.v_mut()).l;
      _loop_s = next(_loop_s);
      _loop_n = n_;
      continue;
    }
  }
  return std::move(*_root);
}

uint64_t GbInterp::lookup(const List<uint64_t> &env, uint64_t i) {
  // Loop replaces the tail recursion: each recursive call updates the loop
  // variables.
  uint64_t _loop_i = i;
  const List<uint64_t> *_loop_env = &env;
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_env->v())) {
      return UINT64_C(0);
    } else {
      const auto &[a0, a1] =
          std::get<typename List<uint64_t>::Cons>(_loop_env->v());
      if (_loop_i <= 0) {
        return std::move(a0);
      } else {
        uint64_t j = _loop_i - 1;
        _loop_i = j;
        _loop_env = crane_raw(a1);
      }
    }
  }
}

List<GbInterp::instr> GbInterp::compile(const GbInterp::expr &e,
                                        const List<GbInterp::instr> &k) {
  // Explicit stack replaces the non-tail recursion of compile: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    List<GbInterp::instr> k;
    const GbInterp::expr *e;
  };

  struct _after_compile_in_Add {
    const GbInterp::expr *a0;
  };

  struct _after_compile_in_Let {
    const GbInterp::expr *e0;
  };

  struct _after_compile_in_Mul {
    const GbInterp::expr *a0;
  };

  using _frame = std::variant<_call, _after_compile_in_Add,
                              _after_compile_in_Let, _after_compile_in_Mul>;
  List<GbInterp::instr> _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{k, &e});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const List<GbInterp::instr> &k = _f.k;
      const GbInterp::expr &e = *_f.e;
      if (std::holds_alternative<typename GbInterp::expr::Num>(e.v())) {
        const auto &[n0] = std::get<typename GbInterp::expr::Num>(e.v());
        _result = List<GbInterp::instr>::cons(instr::ipush(n0), k);
      } else if (std::holds_alternative<typename GbInterp::expr::Var>(e.v())) {
        const auto &[i0] = std::get<typename GbInterp::expr::Var>(e.v());
        _result = List<GbInterp::instr>::cons(instr::iload(i0), k);
      } else if (std::holds_alternative<typename GbInterp::expr::Add>(e.v())) {
        const auto &[a0, b0] = std::get<typename GbInterp::expr::Add>(e.v());
        _stack.emplace_back(_after_compile_in_Add{crane_raw(a0)});
        _stack.emplace_back(
            _call{List<GbInterp::instr>::cons(instr::iadd(), k),
                  crane_raw(b0)});
      } else if (std::holds_alternative<typename GbInterp::expr::Mul>(e.v())) {
        const auto &[a0, b0] = std::get<typename GbInterp::expr::Mul>(e.v());
        _stack.emplace_back(_after_compile_in_Mul{crane_raw(a0)});
        _stack.emplace_back(
            _call{List<GbInterp::instr>::cons(instr::imul(), k),
                  crane_raw(b0)});
      } else if (std::holds_alternative<typename GbInterp::expr::Let>(e.v())) {
        const auto &[e0, body0] = std::get<typename GbInterp::expr::Let>(e.v());
        _stack.emplace_back(_after_compile_in_Let{crane_raw(e0)});
        _stack.emplace_back(_call{
            List<GbInterp::instr>::cons(instr::iunbind(), k),
            crane_raw(body0)});
      } else {
        const auto &[_, t0, _] = std::get<typename GbInterp::expr::If0>(e.v());
        _stack.emplace_back(_call{k, crane_raw(t0)});
      }
    } else if (std::holds_alternative<_after_compile_in_Add>(_popped)) {
      auto _f = std::move(std::get<_after_compile_in_Add>(_popped));
      _stack.pop_back();
      const GbInterp::expr &a0 = *_f.a0;
      _stack.emplace_back(_call{std::move(_result), &a0});
    } else if (std::holds_alternative<_after_compile_in_Let>(_popped)) {
      auto _f = std::move(std::get<_after_compile_in_Let>(_popped));
      _stack.pop_back();
      const GbInterp::expr &e0 = *_f.e0;
      _stack.emplace_back(_call{
          List<GbInterp::instr>::cons(instr::ibind(), std::move(_result)),
          &e0});
    } else {
      auto _f = std::move(std::get<_after_compile_in_Mul>(_popped));
      _stack.pop_back();
      const GbInterp::expr &a0 = *_f.a0;
      _stack.emplace_back(_call{std::move(_result), &a0});
    }
  }
  return _result;
}

uint64_t GbInterp::run(uint64_t fuel, const List<GbInterp::instr> &code,
                       const List<uint64_t> &stack, const List<uint64_t> &env) {
  // Loop replaces the tail recursion: each recursive call updates the loop
  // variables.
  List<uint64_t> _loop_env = env;
  List<uint64_t> _loop_stack = stack;
  const List<GbInterp::instr> *_loop_code = &code;
  uint64_t _loop_fuel = fuel;
  while (true) {
    if (_loop_fuel <= 0) {
      return UINT64_C(0);
    } else {
      uint64_t f = _loop_fuel - 1;
      if (std::holds_alternative<typename List<GbInterp::instr>::Nil>(
              _loop_code->v())) {
        return _loop_stack.hd(UINT64_C(0));
      } else {
        const auto &[a0, a1] =
            std::get<typename List<GbInterp::instr>::Cons>(_loop_code->v());
        const List<GbInterp::instr> &a1_value = *a1;
        if (std::holds_alternative<typename GbInterp::instr::IPush>(a0.v())) {
          const auto &[n0] = std::get<typename GbInterp::instr::IPush>(a0.v());
          _loop_stack = List<uint64_t>::cons(n0, std::move(_loop_stack));
          _loop_code = &a1_value;
          _loop_fuel = f;
        } else if (
                std::holds_alternative<typename GbInterp::instr::ILoad>(a0.v())) {
          const auto &[i1] = std::get<typename GbInterp::instr::ILoad>(a0.v());
          _loop_stack = List<uint64_t>::cons(lookup(_loop_env, i1),
                                             std::move(_loop_stack));
          _loop_code = &a1_value;
          _loop_fuel = f;
        } else if (
                std::holds_alternative<typename GbInterp::instr::IAdd>(a0.v())) {
          _loop_stack = binop(
              [](uint64_t a, uint64_t b) {
                auto &&_once1 = (a + b);
                auto &&_once2 = UINT64_C(4096);
                return (_once2 ? _once1 % _once2 : _once1);
              },
              std::move(_loop_stack));
          _loop_code = &a1_value;
          _loop_fuel = f;
        } else if (
                std::holds_alternative<typename GbInterp::instr::IMul>(a0.v())) {
          _loop_stack = binop(
              [](uint64_t a, uint64_t b) {
                auto &&_once3 = (a * b);
                auto &&_once4 = UINT64_C(4096);
                return (_once4 ? _once3 % _once4 : _once3);
              },
              std::move(_loop_stack));
          _loop_code = &a1_value;
          _loop_fuel = f;
        } else if (
                std::holds_alternative<typename GbInterp::instr::IBind>(a0.v())) {
          List<uint64_t> _next_stack = _loop_stack.tl();
          _loop_env = List<uint64_t>::cons(_loop_stack.hd(UINT64_C(0)),
                                           std::move(_loop_env));
          _loop_code = &a1_value;
          _loop_fuel = f;
          _loop_stack = std::move(_next_stack);
        } else {
          _loop_env = _loop_env.tl();
          _loop_code = &a1_value;
          _loop_fuel = f;
        }
      }
    }
  }
}

GbInterp::expr GbInterp::gen(uint64_t depth, uint64_t s) {
  // Explicit stack replaces the non-tail recursion of gen: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    uint64_t s;
    uint64_t depth;
  };

  struct _after_gen_in_O {
    uint64_t d;
    uint64_t s_;
  };

  struct _after_gen_in_O_2 {
    GbInterp::expr _tmp2;
  };

  struct _after_gen_in_O_3 {};

  struct _after_gen_in_O_4 {
    uint64_t d;
    uint64_t s_;
  };

  struct _after_gen_in_O_5 {
    GbInterp::expr _tmp5;
  };

  struct _after_gen_in_O_6 {
    uint64_t d;
    uint64_t s_;
  };

  struct _after_gen_in_O_7 {
    GbInterp::expr _tmp7;
  };

  struct _after_gen_in_S {};

  using _frame =
      std::variant<_call, _after_gen_in_O, _after_gen_in_O_2, _after_gen_in_O_3,
                   _after_gen_in_O_4, _after_gen_in_O_5, _after_gen_in_O_6,
                   _after_gen_in_O_7, _after_gen_in_S>;
  GbInterp::expr _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{s, depth});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      uint64_t s = _f.s;
      uint64_t depth = _f.depth;
      if (depth <= 0) {
        if ((UINT64_C(3) ? s % UINT64_C(3) : s) == UINT64_C(0)) {
          _result = expr::var((UINT64_C(4) ? s % UINT64_C(4) : s));
        } else {
          _result = expr::num((UINT64_C(7) ? s % UINT64_C(7) : s));
        }
      } else {
        uint64_t d = depth - 1;
        uint64_t s_ = next(s);
        auto _cs = (UINT64_C(5) ? s % UINT64_C(5) : s);
        if (_cs <= 0) {
          _stack.emplace_back(_after_gen_in_O{d, s_});
          _stack.emplace_back(_call{s_, d});
        } else {
          uint64_t n = _cs - 1;
          if (n <= 0) {
            _stack.emplace_back(_after_gen_in_O_3{});
            _stack.emplace_back(_call{s_, d});
          } else {
            uint64_t n0 = n - 1;
            if (n0 <= 0) {
              _stack.emplace_back(_after_gen_in_O_4{d, s_});
              _stack.emplace_back(_call{s_, d});
            } else {
              uint64_t n1 = n0 - 1;
              if (n1 <= 0) {
                _stack.emplace_back(_after_gen_in_O_6{d, s_});
                _stack.emplace_back(_call{s_, d});
              } else {
                uint64_t _x = n1 - 1;
                _stack.emplace_back(_after_gen_in_S{});
                _stack.emplace_back(_call{s_, d});
              }
            }
          }
        }
      }
    } else if (std::holds_alternative<_after_gen_in_O>(_popped)) {
      auto _f = std::move(std::get<_after_gen_in_O>(_popped));
      _stack.pop_back();
      uint64_t d = _f.d;
      uint64_t s_ = _f.s_;
      _stack.emplace_back(_after_gen_in_O_2{std::move(_result)});
      _stack.emplace_back(_call{next(s_), d});
    } else if (std::holds_alternative<_after_gen_in_O_2>(_popped)) {
      auto _f = std::move(std::get<_after_gen_in_O_2>(_popped));
      _stack.pop_back();
      _result = expr::add(std::move(_f._tmp2), std::move(_result));
    } else if (std::holds_alternative<_after_gen_in_O_3>(_popped)) {
      auto _f = std::move(std::get<_after_gen_in_O_3>(_popped));
      _stack.pop_back();
      _result = expr::mul(std::move(_result), expr::num(UINT64_C(1)));
    } else if (std::holds_alternative<_after_gen_in_O_4>(_popped)) {
      auto _f = std::move(std::get<_after_gen_in_O_4>(_popped));
      _stack.pop_back();
      uint64_t d = _f.d;
      uint64_t s_ = _f.s_;
      _stack.emplace_back(_after_gen_in_O_5{std::move(_result)});
      _stack.emplace_back(_call{next(s_), d});
    } else if (std::holds_alternative<_after_gen_in_O_5>(_popped)) {
      auto _f = std::move(std::get<_after_gen_in_O_5>(_popped));
      _stack.pop_back();
      _result = expr::let(std::move(_f._tmp5), std::move(_result));
    } else if (std::holds_alternative<_after_gen_in_O_6>(_popped)) {
      auto _f = std::move(std::get<_after_gen_in_O_6>(_popped));
      _stack.pop_back();
      uint64_t d = _f.d;
      uint64_t s_ = _f.s_;
      _stack.emplace_back(_after_gen_in_O_7{std::move(_result)});
      _stack.emplace_back(_call{next(s_), d});
    } else if (std::holds_alternative<_after_gen_in_O_7>(_popped)) {
      auto _f = std::move(std::get<_after_gen_in_O_7>(_popped));
      _stack.pop_back();
      _result = expr::if0(std::move(_f._tmp7), std::move(_result),
                          expr::num(UINT64_C(0)));
    } else {
      auto _f = std::move(std::get<_after_gen_in_S>(_popped));
      _stack.pop_back();
      _result = expr::add(expr::num(UINT64_C(0)), std::move(_result));
    }
  }
  return _result;
}

uint64_t GbInterp::round(uint64_t depth, uint64_t i) {
  GbInterp::expr e = gen(depth, (i + UINT64_C(3)));
  GbInterp::expr e_ = e.simplify();
  return (
      (
          e.eval(List<uint64_t>::cons(
              UINT64_C(1),
              List<uint64_t>::cons(
                  UINT64_C(2),
                  List<uint64_t>::cons(
                      UINT64_C(3),
                      List<uint64_t>::cons(UINT64_C(4),
                                           List<uint64_t>::nil()))))) +
          e_.eval(List<uint64_t>::cons(
              UINT64_C(1),
              List<uint64_t>::cons(
                  UINT64_C(2),
                  List<uint64_t>::cons(
                      UINT64_C(3),
                      List<uint64_t>::cons(UINT64_C(4),
                                           List<uint64_t>::nil())))))) +
      run(UINT64_C(100000000), compile(e_, List<GbInterp::instr>::nil()),
          List<uint64_t>::nil(),
          List<uint64_t>::cons(
              UINT64_C(1),
              List<uint64_t>::cons(
                  UINT64_C(2),
                  List<uint64_t>::cons(
                      UINT64_C(3),
                      List<uint64_t>::cons(UINT64_C(4),
                                           List<uint64_t>::nil()))))));
}

uint64_t GbInterp::interp(uint64_t depth, uint64_t rounds) {
  return ListDef::seq(UINT64_C(0), rounds).template fold_left<uint64_t>(
      [=](uint64_t acc, uint64_t i) { return (acc + round(depth, i)); },
      UINT64_C(0));
}

List<uint64_t> ListDef::seq(uint64_t start, uint64_t len) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
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
          (_write ? *(*_write =
                          std::make_shared<List<uint64_t>>(std::move(_cell)))
                  : _root.emplace(std::move(_cell)));
      _write = &std::get<typename List<uint64_t>::Cons>(_node.v_mut()).l;
      _loop_len = len0;
      _loop_start = (_loop_start + 1);
      continue;
    }
  }
  return std::move(*_root);
}
