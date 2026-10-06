#include "reuse_list_shapes.h"

List<uint64_t> ReuseListShapes::bump(List<uint64_t> l) {
  crane::rc<List<uint64_t>> _head{};
  crane::rc<List<uint64_t>> *_write = &_head;
  crane::rc<List<uint64_t>> _own = crane::rc<List<uint64_t>>();
  bool _uniq = true;
  const List<uint64_t> *_loop_l = &l;
  while (true) {
    if (crane::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
      *_write = crane::make_rc<List<uint64_t>>(List<uint64_t>::nil());
      break;
    } else {
      const auto &[a0, a1] =
          crane::get<typename List<uint64_t>::Cons>(_loop_l->v());
      auto _rs = crane::reuse_step(_own, _uniq, a1);
      auto _cell = crane::make_rc_reusing_unchecked(
          std::move(_rs.token),
          typename List<uint64_t>::Cons((crane::unbox(a0) + 1), nullptr));
      *_write = std::move(_cell);
      _write = &crane::get<typename List<uint64_t>::Cons>((*_write)->v_mut()).l;
      _own = std::move(std::move(_rs.next));
      _loop_l = _own.get();
      continue;
    }
  }
  return std::move(*_head);
}

List<uint64_t> ReuseListShapes::take(uint64_t n, List<uint64_t> l) {
  if (l.v().index() == 1) {
    if (crane::get<typename List<uint64_t>::Cons>(l.v_mut()).l.use_count() ==
        1) {
      uint64_t x =
          crane::unbox(crane::get<typename List<uint64_t>::Cons>(l.v_mut()).a);
      List<uint64_t> t =
          std::move(*crane::get<typename List<uint64_t>::Cons>(l.v_mut()).l);
      if (n <= 0) {
        return List<uint64_t>::nil();
      } else {
        uint64_t m = n - 1;
        return List<uint64_t>::cons_crane_reuse(
            std::move(crane::get<typename List<uint64_t>::Cons>(l.v_mut()).l),
            x, take(m, std::move(t)));
      }
    } else {
      if (crane::holds_alternative<typename List<uint64_t>::Nil>(l.v_mut())) {
        return List<uint64_t>::nil();
      } else {
        auto &[a0, a1] = crane::get<typename List<uint64_t>::Cons>(l.v_mut());
        if (n <= 0) {
          return List<uint64_t>::nil();
        } else {
          uint64_t m = n - 1;
          return List<uint64_t>::cons(crane::unbox(a0), take(m, *a1));
        }
      }
    }
  } else {
    if (crane::holds_alternative<typename List<uint64_t>::Nil>(l.v_mut())) {
      return List<uint64_t>::nil();
    } else {
      auto &[a0, a1] = crane::get<typename List<uint64_t>::Cons>(l.v_mut());
      if (n <= 0) {
        return List<uint64_t>::nil();
      } else {
        uint64_t m = n - 1;
        return List<uint64_t>::cons(crane::unbox(a0), take(m, *a1));
      }
    }
  }
}

ReuseListShapes::frames
ReuseListShapes::add_to_frame(const ReuseListShapes::mem &m, uint64_t k) {
  const ReuseListShapes::frames &s = m.stack;
  if (crane::holds_alternative<typename ReuseListShapes::frames::Single>(
          s.v())) {
    const auto &[a0] =
        crane::get<typename ReuseListShapes::frames::Single>(s.v());
    return frames::single(List<uint64_t>::cons(k, *a0));
  } else {
    const auto &[a0, a1] =
        crane::get<typename ReuseListShapes::frames::Push>(s.v());
    return frames::push(List<uint64_t>::cons(k, *a0), *a1);
  }
}

ReuseListShapes::frames
ReuseListShapes::add_to_frame_(const ReuseListShapes::mem &m, uint64_t k) {
  const ReuseListShapes::frames &s = m.stack;
  const crane::obj &_x = m.top;
  if (crane::holds_alternative<typename ReuseListShapes::frames::Single>(
          s.v())) {
    const auto &[a0] =
        crane::get<typename ReuseListShapes::frames::Single>(s.v());
    return frames::single(List<uint64_t>::cons(k, *a0));
  } else {
    const auto &[a0, a1] =
        crane::get<typename ReuseListShapes::frames::Push>(s.v());
    return frames::push(List<uint64_t>::cons(k, *a0), *a1);
  }
}
