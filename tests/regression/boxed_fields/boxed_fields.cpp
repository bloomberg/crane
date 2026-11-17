#include "boxed_fields.h"

List<BoxedFields::point>
BoxedFields::shift(uint64_t d, const List<BoxedFields::point> &ps) {
  std::optional<List<BoxedFields::point>> _root{};
  std::shared_ptr<List<BoxedFields::point>> *_write = nullptr;
  const List<BoxedFields::point> *_loop_ps = &ps;
  while (true) {
    if (std::holds_alternative<typename List<BoxedFields::point>::Nil>(
            _loop_ps->v())) {
      auto _value = List<BoxedFields::point>::nil();
      (_write ? *(*_write = std::make_shared<List<BoxedFields::point>>(
                      std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<BoxedFields::point>::Cons>(_loop_ps->v());
      const auto &_sv0 = crane::unbox(a0);
      const auto &[a00, a10] = _sv0;
      auto _cell = typename List<BoxedFields::point>::Cons(
          point::pt((a00 + d), a10), nullptr);
      List<BoxedFields::point> &_node =
          (_write ? *(*_write = std::make_shared<List<BoxedFields::point>>(
                          std::move(_cell)))
                  : _root.emplace(std::move(_cell)));
      _write =
          &std::get<typename List<BoxedFields::point>::Cons>(_node.v_mut()).l;
      _loop_ps = crane_raw(a1);
      continue;
    }
  }
  return std::move(*_root);
}
