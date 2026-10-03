#include "boxed_fields.h"

List<BoxedFields::point>
BoxedFields::shift(uint64_t d, const List<BoxedFields::point> &ps) {
  std::shared_ptr<List<BoxedFields::point>> _head{};
  std::shared_ptr<List<BoxedFields::point>> *_write = &_head;
  const List<BoxedFields::point> *_loop_ps = &ps;
  while (true) {
    if (std::holds_alternative<typename List<BoxedFields::point>::Nil>(
            _loop_ps->v())) {
      *_write = std::make_shared<List<BoxedFields::point>>(
          List<BoxedFields::point>::nil());
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<BoxedFields::point>::Cons>(_loop_ps->v());
      const auto &[a00, a10] = a0;
      auto _cell = std::make_shared<List<BoxedFields::point>>(
          typename List<BoxedFields::point>::Cons(point::pt((a00 + d), a10),
                                                  nullptr));
      *_write = std::move(_cell);
      _write =
          &std::get<typename List<BoxedFields::point>::Cons>((*_write)->v_mut())
               .l;
      _loop_ps = crane_raw(a1);
      continue;
    }
  }
  return std::move(*_head);
}
