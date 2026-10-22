#include "reuse_token_in_closure.h"

uint64_t ReuseTokenInClosure::suml(const ReuseTokenInClosure::lst &l) {
  if (std::holds_alternative<typename ReuseTokenInClosure::lst::Nil>(l.v())) {
    return UINT64_C(0);
  } else {
    const auto &[a0, a1] =
        std::get<typename ReuseTokenInClosure::lst::Cons>(l.v());
    return (a0 + suml(*a1));
  }
}

ReuseTokenInClosure::lst ReuseTokenInClosure::g(ReuseTokenInClosure::lst l) {
  if (l.v().index() == 1) {
    if (std::get<typename ReuseTokenInClosure::lst::Cons>(l.v_mut())
            .a1.use_count() == 1) {
      uint64_t x = std::move(
          std::get<typename ReuseTokenInClosure::lst::Cons>(l.v_mut()).a0);
      ReuseTokenInClosure::lst t = std::move(
          *std::get<typename ReuseTokenInClosure::lst::Cons>(l.v_mut()).a1);
      return lst::cons_crane_reuse(
          std::move(
              std::get<typename ReuseTokenInClosure::lst::Cons>(l.v_mut()).a1),
          twice([=](uint64_t y) { return suml(lst::cons(y, t)); },
                std::move(x)),
          g(t));
    } else {
      if (std::holds_alternative<typename ReuseTokenInClosure::lst::Nil>(
              l.v_mut())) {
        return lst::nil();
      } else {
        auto &[a0, a1] =
            std::get<typename ReuseTokenInClosure::lst::Cons>(l.v_mut());
        const ReuseTokenInClosure::lst &a1_value = *a1;
        return lst::cons(
            twice([=](uint64_t y) { return suml(lst::cons(y, a1_value)); },
                  std::move(a0)),
            g(a1_value));
      }
    }
  } else {
    if (std::holds_alternative<typename ReuseTokenInClosure::lst::Nil>(
            l.v_mut())) {
      return lst::nil();
    } else {
      auto &[a0, a1] =
          std::get<typename ReuseTokenInClosure::lst::Cons>(l.v_mut());
      const ReuseTokenInClosure::lst &a1_value = *a1;
      return lst::cons(
          twice([=](uint64_t y) { return suml(lst::cons(y, a1_value)); },
                std::move(a0)),
          g(a1_value));
    }
  }
}

ReuseTokenInClosure::lst ReuseTokenInClosure::h(ReuseTokenInClosure::lst l) {
  if (l.v().index() == 1) {
    if (std::get<typename ReuseTokenInClosure::lst::Cons>(l.v_mut())
            .a1.use_count() == 1) {
      uint64_t x = std::move(
          std::get<typename ReuseTokenInClosure::lst::Cons>(l.v_mut()).a0);
      ReuseTokenInClosure::lst t = std::move(
          *std::get<typename ReuseTokenInClosure::lst::Cons>(l.v_mut()).a1);
      return lst::cons_crane_reuse(
          std::move(
              std::get<typename ReuseTokenInClosure::lst::Cons>(l.v_mut()).a1),
          suml(lst::cons(x, lst::cons(x, lst::nil()))), h(std::move(t)));
    } else {
      if (std::holds_alternative<typename ReuseTokenInClosure::lst::Nil>(
              l.v_mut())) {
        return lst::nil();
      } else {
        auto &[a0, a1] =
            std::get<typename ReuseTokenInClosure::lst::Cons>(l.v_mut());
        return lst::cons(suml(lst::cons(a0, lst::cons(a0, lst::nil()))),
                         h(*a1));
      }
    }
  } else {
    if (std::holds_alternative<typename ReuseTokenInClosure::lst::Nil>(
            l.v_mut())) {
      return lst::nil();
    } else {
      auto &[a0, a1] =
          std::get<typename ReuseTokenInClosure::lst::Cons>(l.v_mut());
      return lst::cons(suml(lst::cons(a0, lst::cons(a0, lst::nil()))), h(*a1));
    }
  }
}

ReuseTokenInClosure::lst ReuseTokenInClosure::upto(uint64_t n) {
  if (n <= 0) {
    return lst::nil();
  } else {
    uint64_t k = n - 1;
    return lst::cons(n, upto(k));
  }
}
