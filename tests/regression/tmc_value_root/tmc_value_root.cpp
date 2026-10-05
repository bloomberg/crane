#include "tmc_value_root.h"

TmcValueRoot::lst TmcValueRoot::range(uint64_t start, uint64_t count) {
  std::optional<TmcValueRoot::lst> _root{};
  std::shared_ptr<TmcValueRoot::lst> *_write = nullptr;
  uint64_t _loop_count = std::move(count);
  uint64_t _loop_start = std::move(start);
  while (true) {
    if (_loop_count <= 0) {
      auto _value = lst::nil();
      (_write
           ? *(*_write = std::make_shared<TmcValueRoot::lst>(std::move(_value)))
           : _root.emplace(std::move(_value)));
      break;
    } else {
      uint64_t c = _loop_count - 1;
      auto _cell = typename TmcValueRoot::lst::Cons(_loop_start, nullptr);
      TmcValueRoot::lst &_node =
          (_write ? *(*_write =
                          std::make_shared<TmcValueRoot::lst>(std::move(_cell)))
                  : _root.emplace(std::move(_cell)));
      _write = &std::get<typename TmcValueRoot::lst::Cons>(_node.v_mut()).l;
      _loop_count = c;
      _loop_start = (_loop_start + 1);
      continue;
    }
  }
  return std::move(*_root);
}

TmcValueRoot::lst TmcValueRoot::app(const TmcValueRoot::lst &xs,
                                    TmcValueRoot::lst ys) {
  std::optional<TmcValueRoot::lst> _root{};
  std::shared_ptr<TmcValueRoot::lst> *_write = nullptr;
  TmcValueRoot::lst _loop_ys = std::move(ys);
  const TmcValueRoot::lst *_loop_xs = &xs;
  while (true) {
    if (std::holds_alternative<typename TmcValueRoot::lst::Nil>(
            _loop_xs->v())) {
      auto _value = std::move(_loop_ys);
      (_write
           ? *(*_write = std::make_shared<TmcValueRoot::lst>(std::move(_value)))
           : _root.emplace(std::move(_value)));
      break;
    } else {
      const auto &[x0, l] =
          std::get<typename TmcValueRoot::lst::Cons>(_loop_xs->v());
      auto _cell = typename TmcValueRoot::lst::Cons(x0, nullptr);
      TmcValueRoot::lst &_node =
          (_write ? *(*_write =
                          std::make_shared<TmcValueRoot::lst>(std::move(_cell)))
                  : _root.emplace(std::move(_cell)));
      _write = &std::get<typename TmcValueRoot::lst::Cons>(_node.v_mut()).l;
      _loop_xs = crane_raw(l);
      continue;
    }
  }
  return std::move(*_root);
}

/// Two cells per step: the second is allocated and linked into the first.
TmcValueRoot::lst TmcValueRoot::stutter(const TmcValueRoot::lst &xs) {
  std::optional<TmcValueRoot::lst> _root{};
  std::shared_ptr<TmcValueRoot::lst> *_write = nullptr;
  const TmcValueRoot::lst *_loop_xs = &xs;
  while (true) {
    if (std::holds_alternative<typename TmcValueRoot::lst::Nil>(
            _loop_xs->v())) {
      auto _value = lst::nil();
      (_write
           ? *(*_write = std::make_shared<TmcValueRoot::lst>(std::move(_value)))
           : _root.emplace(std::move(_value)));
      break;
    } else {
      const auto &[x0, l] =
          std::get<typename TmcValueRoot::lst::Cons>(_loop_xs->v());
      auto _cell1 = std::make_shared<TmcValueRoot::lst>(
          typename TmcValueRoot::lst::Cons(x0, nullptr));
      auto _cell = typename TmcValueRoot::lst::Cons(x0, std::move(_cell1));
      TmcValueRoot::lst &_node =
          (_write ? *(*_write =
                          std::make_shared<TmcValueRoot::lst>(std::move(_cell)))
                  : _root.emplace(std::move(_cell)));
      _write = &std::get<typename TmcValueRoot::lst::Cons>(
                    std::get<typename TmcValueRoot::lst::Cons>(_node.v_mut())
                        .l->v_mut())
                    .l;
      _loop_xs = crane_raw(l);
      continue;
    }
  }
  return std::move(*_root);
}
