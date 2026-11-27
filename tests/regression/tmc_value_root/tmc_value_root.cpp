#include "tmc_value_root.h"

TmcValueRoot::lst TmcValueRoot::range(uint64_t start, uint64_t count) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
  std::optional<TmcValueRoot::lst> _root{};
  std::shared_ptr<TmcValueRoot::lst> *_write = nullptr;
  while (true) {
    if (count <= 0) {
      auto _value = lst::nil();
      (_write ? *(*_write =
                      std::make_shared<TmcValueRoot::lst>(std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      uint64_t c = count - 1;
      auto _cell = typename TmcValueRoot::lst::Cons(start, nullptr);
      TmcValueRoot::lst &_node =
          (_write ? *(*_write =
                          std::make_shared<TmcValueRoot::lst>(std::move(_cell)))
                  : _root.emplace(std::move(_cell)));
      _write = &std::get<typename TmcValueRoot::lst::Cons>(_node.v_mut()).l;
      count = c;
      start = (start + 1);
      continue;
    }
  }
  return std::move(*_root);
}

TmcValueRoot::lst TmcValueRoot::app(const TmcValueRoot::lst &xs,
                                    TmcValueRoot::lst ys) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
  std::optional<TmcValueRoot::lst> _root{};
  std::shared_ptr<TmcValueRoot::lst> *_write = nullptr;
  const TmcValueRoot::lst *_loop_xs = &xs;
  while (true) {
    if (std::holds_alternative<typename TmcValueRoot::lst::Nil>(_loop_xs->v())) {
      auto _value = std::move(ys);
      (_write ? *(*_write =
                      std::make_shared<TmcValueRoot::lst>(std::move(_value)))
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
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
  std::optional<TmcValueRoot::lst> _root{};
  std::shared_ptr<TmcValueRoot::lst> *_write = nullptr;
  const TmcValueRoot::lst *_loop_xs = &xs;
  while (true) {
    if (std::holds_alternative<typename TmcValueRoot::lst::Nil>(_loop_xs->v())) {
      auto _value = lst::nil();
      (_write ? *(*_write =
                      std::make_shared<TmcValueRoot::lst>(std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      const auto &[x0, l] =
          std::get<typename TmcValueRoot::lst::Cons>(_loop_xs->v());
      auto _cell = typename TmcValueRoot::lst::Cons(
          x0, std::make_shared<TmcValueRoot::lst>(
                  typename TmcValueRoot::lst::Cons(x0, nullptr)));
      TmcValueRoot::lst &_node =
          (_write ? *(*_write =
                          std::make_shared<TmcValueRoot::lst>(std::move(_cell)))
                  : _root.emplace(std::move(_cell)));
      _write =
          &std::get<typename TmcValueRoot::lst::Cons>(std::get<
              typename TmcValueRoot::lst::Cons>(_node.v_mut()).l->v_mut())
              .l;
      _loop_xs = crane_raw(l);
      continue;
    }
  }
  return std::move(*_root);
}
