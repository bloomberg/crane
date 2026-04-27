#include <sort.h>

__attribute__((pure)) Sig<List<unsigned int>>
Sort::sort_cons_prog(unsigned int a, const List<unsigned int> &,
                     const List<unsigned int> &l_) {
  if (std::holds_alternative<typename List<unsigned int>::Nil>(l_.v())) {
    return Sig<List<unsigned int>>::exist(
        List<unsigned int>::cons(a, List<unsigned int>::nil()));
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename List<unsigned int>::Cons>(l_.v());
    Sig<List<unsigned int>> s = sort_cons_prog(a, *(d_a1), *(d_a1));
    const auto &[d_x0] =
        std::get<typename Sig<List<unsigned int>>::Exist>(s.v());
    bool s0 = Compare_dec::le_lt_dec(a, d_a0);
    if (s0) {
      return Sig<List<unsigned int>>::exist(
          List<unsigned int>::cons(a, List<unsigned int>::cons(d_a0, *(d_a1))));
    } else {
      return Sig<List<unsigned int>>::exist(
          List<unsigned int>::cons(d_a0, d_x0));
    }
  }
}

__attribute__((pure)) Sig<List<unsigned int>>
Sort::isort(const List<unsigned int> &l) {
  if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
    return Sig<List<unsigned int>>::exist(List<unsigned int>::nil());
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename List<unsigned int>::Cons>(l.v());
    auto &&_sv0 = isort(*(d_a1));
    const auto &[d_x0] =
        std::get<typename Sig<List<unsigned int>>::Exist>(_sv0.v());
    return sort_cons_prog(d_a0, *(d_a1), d_x0);
  }
}

__attribute__((pure)) List<unsigned int>
Sort::merge(List<unsigned int> l1, const List<unsigned int> &l2) {
  std::function<List<unsigned int>(List<unsigned int>)> merge_aux;
  merge_aux = [&](List<unsigned int> l3) -> List<unsigned int> {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(l1.v())) {
      return l3;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(l1.v());
      if (std::holds_alternative<typename List<unsigned int>::Nil>(l3.v())) {
        return l1;
      } else {
        const auto &[d_a00, d_a10] =
            std::get<typename List<unsigned int>::Cons>(l3.v());
        if (Compare_dec::le_lt_dec(d_a0, d_a00)) {
          return List<unsigned int>::cons(d_a0, merge(*(d_a1), l3));
        } else {
          return List<unsigned int>::cons(d_a00, merge_aux(*(d_a10)));
        }
      }
    }
  };
  return merge_aux(l2);
}

__attribute__((pure)) Sig<List<unsigned int>>
Sort::merge_prog(const List<unsigned int> &, const List<unsigned int> &l1,
                 const List<unsigned int> &l2) {
  return Sig<List<unsigned int>>::exist(merge(l1, l2));
}

__attribute__((pure)) Sig<List<unsigned int>>
Sort::msort(const List<unsigned int> &_x0) {
  return div_conq_split(
      Sig<List<unsigned int>>::exist(List<unsigned int>::nil()),
      [](unsigned int a) {
        return Sig<List<unsigned int>>::exist(
            List<unsigned int>::cons(a, List<unsigned int>::nil()));
      },
      [](const List<unsigned int> &ls, const Sig<List<unsigned int>> &x,
         const Sig<List<unsigned int>> &x0) {
        const auto &[d_x] =
            std::get<typename Sig<List<unsigned int>>::Exist>(x.v());
        const auto &[d_x0] =
            std::get<typename Sig<List<unsigned int>>::Exist>(x0.v());
        return merge_prog(ls, d_x, d_x0);
      },
      _x0);
}

__attribute__((pure)) Sig<List<unsigned int>>
Sort::pair_merge_prog(const unsigned int &, const unsigned int &,
                      const List<unsigned int> &, const List<unsigned int> &l_,
                      const List<unsigned int> &l_0) {
  return Sig<List<unsigned int>>::exist(merge(l_0, l_));
}

__attribute__((pure)) Sig<List<unsigned int>>
Sort::psort(const List<unsigned int> &_x0) {
  return div_conq_pair(
      Sig<List<unsigned int>>::exist(List<unsigned int>::nil()),
      [](unsigned int a) {
        return Sig<List<unsigned int>>::exist(
            List<unsigned int>::cons(a, List<unsigned int>::nil()));
      },
      [](unsigned int a1, unsigned int a2) {
        bool s = Compare_dec::le_lt_dec(a1, a2);
        if (s) {
          return Sig<List<unsigned int>>::exist(List<unsigned int>::cons(
              a1, List<unsigned int>::cons(a2, List<unsigned int>::nil())));
        } else {
          return Sig<List<unsigned int>>::exist(List<unsigned int>::cons(
              a2, List<unsigned int>::cons(a1, List<unsigned int>::nil())));
        }
      },
      [](const unsigned int &a1, const unsigned int &a2,
         const List<unsigned int> &l, const Sig<List<unsigned int>> &x,
         const Sig<List<unsigned int>> &x0) {
        const auto &[d_x] =
            std::get<typename Sig<List<unsigned int>>::Exist>(x.v());
        const auto &[d_x0] =
            std::get<typename Sig<List<unsigned int>>::Exist>(x0.v());
        return pair_merge_prog(a1, a2, l, d_x0, d_x);
      },
      _x0);
}

__attribute__((pure)) Sig<List<unsigned int>>
Sort::qsort(const List<unsigned int> &_x0) {
  return div_conq_pivot(
      Compare_dec::le_dec,
      Sig<List<unsigned int>>::exist(List<unsigned int>::nil()),
      [](unsigned int a, const List<unsigned int> &,
         const Sig<List<unsigned int>> &x, const Sig<List<unsigned int>> &x0) {
        const auto &[d_x] =
            std::get<typename Sig<List<unsigned int>>::Exist>(x.v());
        const auto &[d_x0] =
            std::get<typename Sig<List<unsigned int>>::Exist>(x0.v());
        return Sig<List<unsigned int>>::exist(
            merge(d_x, List<unsigned int>::cons(a, d_x0)));
      },
      _x0);
}

__attribute__((pure)) bool Compare_dec::le_lt_dec(const unsigned int &n,
                                                  const unsigned int &m) {
  if (n <= 0) {
    return true;
  } else {
    unsigned int n0 = n - 1;
    if (m <= 0) {
      return false;
    } else {
      unsigned int n1 = m - 1;
      if (Compare_dec::le_lt_dec(n0, n1)) {
        return true;
      } else {
        return false;
      }
    }
  }
}

__attribute__((pure)) bool Compare_dec::le_gt_dec(const unsigned int &_x0,
                                                  const unsigned int &_x1) {
  return Compare_dec::le_lt_dec(_x0, _x1);
}

__attribute__((pure)) bool Compare_dec::le_dec(const unsigned int &n,
                                               const unsigned int &m) {
  bool s = Compare_dec::le_gt_dec(n, m);
  if (s) {
    return true;
  } else {
    return false;
  }
}
