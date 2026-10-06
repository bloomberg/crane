#include "reuse_list_shapes.h"

Positive Pos::pred_double(Positive x) {
  if (x.v().index() == 0) {
    if (crane::get<typename Positive::XI>(x.v_mut()).a0.use_count() == 1) {
      Positive p = std::move(*crane::get<typename Positive::XI>(x.v_mut()).a0);
      return Positive::xi_crane_reuse(
          std::move(crane::get<typename Positive::XI>(x.v_mut()).a0),
          Positive::xo(std::move(p)));
    } else {
      if (crane::holds_alternative<typename Positive::XI>(x.v_mut())) {
        auto &[a0] = crane::get<typename Positive::XI>(x.v_mut());
        return Positive::xi(Positive::xo(*a0));
      } else if (crane::holds_alternative<typename Positive::XO>(x.v_mut())) {
        auto &[a0] = crane::get<typename Positive::XO>(x.v_mut());
        return Positive::xi(pred_double(*a0));
      } else {
        return Positive::xh();
      }
    }
  } else {
    if (crane::holds_alternative<typename Positive::XI>(x.v_mut())) {
      auto &[a0] = crane::get<typename Positive::XI>(x.v_mut());
      return Positive::xi(Positive::xo(*a0));
    } else if (crane::holds_alternative<typename Positive::XO>(x.v_mut())) {
      auto &[a0] = crane::get<typename Positive::XO>(x.v_mut());
      return Positive::xi(pred_double(*a0));
    } else {
      return Positive::xh();
    }
  }
}

Pos::mask Pos::succ_double_mask(Pos::mask x) {
  if (crane::holds_alternative<typename Pos::mask::IsNul>(x.v_mut())) {
    return mask::ispos(Positive::xh());
  } else if (crane::holds_alternative<typename Pos::mask::IsPos>(x.v_mut())) {
    auto &[a0] = crane::get<typename Pos::mask::IsPos>(x.v_mut());
    return mask::ispos(Positive::xi(*a0));
  } else {
    return mask::isneg();
  }
}

Pos::mask Pos::double_mask(Pos::mask x) {
  if (crane::holds_alternative<typename Pos::mask::IsNul>(x.v_mut())) {
    return mask::isnul();
  } else if (crane::holds_alternative<typename Pos::mask::IsPos>(x.v_mut())) {
    auto &[a0] = crane::get<typename Pos::mask::IsPos>(x.v_mut());
    return mask::ispos(Positive::xo(*a0));
  } else {
    return mask::isneg();
  }
}

Pos::mask Pos::double_pred_mask(const Positive &x) {
  if (crane::holds_alternative<typename Positive::XI>(x.v())) {
    const auto &[a0] = crane::get<typename Positive::XI>(x.v());
    return mask::ispos(Positive::xo(Positive::xo(*a0)));
  } else if (crane::holds_alternative<typename Positive::XO>(x.v())) {
    const auto &[a0] = crane::get<typename Positive::XO>(x.v());
    return mask::ispos(Positive::xo(pred_double(*a0)));
  } else {
    return mask::isnul();
  }
}

Pos::mask Pos::sub_mask(const Positive &x, const Positive &y) {
  if (crane::holds_alternative<typename Positive::XI>(x.v())) {
    const auto &[a0] = crane::get<typename Positive::XI>(x.v());
    if (crane::holds_alternative<typename Positive::XI>(y.v())) {
      const auto &[a00] = crane::get<typename Positive::XI>(y.v());
      return double_mask(sub_mask(*a0, *a00));
    } else if (crane::holds_alternative<typename Positive::XO>(y.v())) {
      const auto &[a00] = crane::get<typename Positive::XO>(y.v());
      return succ_double_mask(sub_mask(*a0, *a00));
    } else {
      return mask::ispos(Positive::xo(*a0));
    }
  } else if (crane::holds_alternative<typename Positive::XO>(x.v())) {
    const auto &[a0] = crane::get<typename Positive::XO>(x.v());
    if (crane::holds_alternative<typename Positive::XI>(y.v())) {
      const auto &[a00] = crane::get<typename Positive::XI>(y.v());
      return succ_double_mask(sub_mask_carry(*a0, *a00));
    } else if (crane::holds_alternative<typename Positive::XO>(y.v())) {
      const auto &[a00] = crane::get<typename Positive::XO>(y.v());
      return double_mask(sub_mask(*a0, *a00));
    } else {
      return mask::ispos(pred_double(*a0));
    }
  } else {
    if (crane::holds_alternative<typename Positive::XH>(y.v())) {
      return mask::isnul();
    } else {
      return mask::isneg();
    }
  }
}

Pos::mask Pos::sub_mask_carry(const Positive &x, const Positive &y) {
  if (crane::holds_alternative<typename Positive::XI>(x.v())) {
    const auto &[a0] = crane::get<typename Positive::XI>(x.v());
    if (crane::holds_alternative<typename Positive::XI>(y.v())) {
      const auto &[a00] = crane::get<typename Positive::XI>(y.v());
      return succ_double_mask(sub_mask_carry(*a0, *a00));
    } else if (crane::holds_alternative<typename Positive::XO>(y.v())) {
      const auto &[a00] = crane::get<typename Positive::XO>(y.v());
      return double_mask(sub_mask(*a0, *a00));
    } else {
      return mask::ispos(pred_double(*a0));
    }
  } else if (crane::holds_alternative<typename Positive::XO>(x.v())) {
    const auto &[a0] = crane::get<typename Positive::XO>(x.v());
    if (crane::holds_alternative<typename Positive::XI>(y.v())) {
      const auto &[a00] = crane::get<typename Positive::XI>(y.v());
      return double_mask(sub_mask_carry(*a0, *a00));
    } else if (crane::holds_alternative<typename Positive::XO>(y.v())) {
      const auto &[a00] = crane::get<typename Positive::XO>(y.v());
      return succ_double_mask(sub_mask_carry(*a0, *a00));
    } else {
      return double_pred_mask(*a0);
    }
  } else {
    return mask::isneg();
  }
}

Comparison Pos::compare_cont(Comparison r, const Positive &x,
                             const Positive &y) {
  if (crane::holds_alternative<typename Positive::XI>(x.v())) {
    const auto &[a0] = crane::get<typename Positive::XI>(x.v());
    if (crane::holds_alternative<typename Positive::XI>(y.v())) {
      const auto &[a00] = crane::get<typename Positive::XI>(y.v());
      return compare_cont(r, *a0, *a00);
    } else if (crane::holds_alternative<typename Positive::XO>(y.v())) {
      const auto &[a00] = crane::get<typename Positive::XO>(y.v());
      return compare_cont(Comparison::GT, *a0, *a00);
    } else {
      return Comparison::GT;
    }
  } else if (crane::holds_alternative<typename Positive::XO>(x.v())) {
    const auto &[a0] = crane::get<typename Positive::XO>(x.v());
    if (crane::holds_alternative<typename Positive::XI>(y.v())) {
      const auto &[a00] = crane::get<typename Positive::XI>(y.v());
      return compare_cont(Comparison::LT, *a0, *a00);
    } else if (crane::holds_alternative<typename Positive::XO>(y.v())) {
      const auto &[a00] = crane::get<typename Positive::XO>(y.v());
      return compare_cont(r, *a0, *a00);
    } else {
      return Comparison::GT;
    }
  } else {
    if (crane::holds_alternative<typename Positive::XH>(y.v())) {
      return r;
    } else {
      return Comparison::LT;
    }
  }
}

Comparison Pos::compare(const Positive &x0_, const Positive &x1_) {
  return compare_cont(Comparison::EQ, x0_, x1_);
}

uint64_t Pos::to_nat(const Positive &x) {
  return iter_op<uint64_t>(
      [](uint64_t _x0, uint64_t _x1) -> uint64_t { return (_x0 + _x1); }, x,
      UINT64_C(1));
}

N BinNat::succ_double(N x) {
  if (crane::holds_alternative<typename N::N0>(x.v_mut())) {
    return N::npos(Positive::xh());
  } else {
    auto &[a0] = crane::get<typename N::Npos>(x.v_mut());
    return N::npos(Positive::xi(*a0));
  }
}

N BinNat::double_(N n) {
  if (crane::holds_alternative<typename N::N0>(n.v_mut())) {
    return N::n0();
  } else {
    auto &[a0] = crane::get<typename N::Npos>(n.v_mut());
    return N::npos(Positive::xo(*a0));
  }
}

N BinNat::sub(N n, N m) {
  if (crane::holds_alternative<typename N::N0>(n.v_mut())) {
    return N::n0();
  } else {
    auto &[a0] = crane::get<typename N::Npos>(n.v_mut());
    if (crane::holds_alternative<typename N::N0>(m.v_mut())) {
      return n;
    } else {
      auto &[a00] = crane::get<typename N::Npos>(m.v_mut());
      auto &&_sv1 = Pos::sub_mask(*a0, *a00);
      if (crane::holds_alternative<typename Pos::mask::IsPos>(_sv1.v())) {
        const auto &[a01] = crane::get<typename Pos::mask::IsPos>(_sv1.v());
        return N::npos(*a01);
      } else {
        return N::n0();
      }
    }
  }
}

Comparison BinNat::compare(const N &n, const N &m) {
  if (crane::holds_alternative<typename N::N0>(n.v())) {
    if (crane::holds_alternative<typename N::N0>(m.v())) {
      return Comparison::EQ;
    } else {
      return Comparison::LT;
    }
  } else {
    const auto &[a0] = crane::get<typename N::Npos>(n.v());
    if (crane::holds_alternative<typename N::N0>(m.v())) {
      return Comparison::GT;
    } else {
      const auto &[a00] = crane::get<typename N::Npos>(m.v());
      return Pos::compare(*a0, *a00);
    }
  }
}

bool BinNat::leb(const N &x, const N &y) {
  switch (BinNat::compare(x, y)) {
  case Comparison::GT: {
    return false;
  }
  default: {
    return true;
  }
  }
}

std::pair<N, N> BinNat::pos_div_eucl(const Positive &a, N b) {
  if (crane::holds_alternative<typename Positive::XI>(a.v())) {
    const auto &[a0] = crane::get<typename Positive::XI>(a.v());
    auto [q, r] = BinNat::pos_div_eucl(*a0, b);
    N r_ = BinNat::succ_double(std::move(r));
    if (BinNat::leb(b, r_)) {
      return std::make_pair(BinNat::succ_double(std::move(q)),
                            BinNat::sub(std::move(r_), std::move(b)));
    } else {
      return std::make_pair(BinNat::double_(std::move(q)), std::move(r_));
    }
  } else if (crane::holds_alternative<typename Positive::XO>(a.v())) {
    const auto &[a0] = crane::get<typename Positive::XO>(a.v());
    auto [q, r] = BinNat::pos_div_eucl(*a0, b);
    N r_ = BinNat::double_(std::move(r));
    if (BinNat::leb(b, r_)) {
      return std::make_pair(BinNat::succ_double(std::move(q)),
                            BinNat::sub(std::move(r_), std::move(b)));
    } else {
      return std::make_pair(BinNat::double_(std::move(q)), std::move(r_));
    }
  } else {
    if (crane::holds_alternative<typename N::N0>(b.v_mut())) {
      return std::make_pair(N::n0(), N::npos(Positive::xh()));
    } else {
      auto &[a00] = crane::get<typename N::Npos>(b.v_mut());
      auto &&_sv = *a00;
      if (crane::holds_alternative<typename Positive::XH>(_sv.v())) {
        return std::make_pair(N::npos(Positive::xh()), N::n0());
      } else {
        return std::make_pair(N::n0(), N::npos(Positive::xh()));
      }
    }
  }
}

std::pair<N, N> BinNat::div_eucl(const N &a, N b) {
  if (crane::holds_alternative<typename N::N0>(a.v())) {
    return std::make_pair(N::n0(), N::n0());
  } else {
    const auto &[a0] = crane::get<typename N::Npos>(a.v());
    if (crane::holds_alternative<typename N::N0>(b.v_mut())) {
      return std::make_pair(N::n0(), a);
    } else {
      return BinNat::pos_div_eucl(*a0, b);
    }
  }
}

N BinNat::div(const N &a, N b) {
  return BinNat::div_eucl(a, std::move(b)).first;
}

uint64_t BinNat::to_nat(const N &a) {
  if (crane::holds_alternative<typename N::N0>(a.v())) {
    return UINT64_C(0);
  } else {
    const auto &[a0] = crane::get<typename N::Npos>(a.v());
    return Pos::to_nat(*a0);
  }
}

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

List<uint64_t> ReuseListShapes::ins(uint64_t k, List<uint64_t> s) {
  if (crane::holds_alternative<typename List<uint64_t>::Nil>(s.v_mut())) {
    return List<uint64_t>::cons(k, List<uint64_t>::nil());
  } else {
    auto &[a0, a1] = crane::get<typename List<uint64_t>::Cons>(s.v_mut());
    if (k < crane::unbox(a0)) {
      return List<uint64_t>::cons(k, s);
    } else {
      if (k == crane::unbox(a0)) {
        return List<uint64_t>::cons(k, *a1);
      } else {
        return List<uint64_t>::cons(crane::unbox(a0), ins(k, *a1));
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
