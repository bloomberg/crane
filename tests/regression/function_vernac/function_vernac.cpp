#include "function_vernac.h"

Sig<uint64_t> FunctionVernac::div2_terminate(uint64_t n) {
  if (n <= 0) {
    return Sig<uint64_t>::exist(UINT64_C(0));
  } else {
    uint64_t n0 = n - 1;
    if (n0 <= 0) {
      return Sig<uint64_t>::exist(UINT64_C(0));
    } else {
      uint64_t n1 = n0 - 1;
      const auto &_sv = div2_terminate(n1);
      const auto &[x0] = _sv;
      return Sig<uint64_t>::exist((x0 + 1));
    }
  }
}

uint64_t FunctionVernac::div2(uint64_t n) {
  const auto &_sv = div2_terminate(n);
  const auto &[x] = _sv;
  return x;
}

FunctionVernac::R_div2 FunctionVernac::R_div2_correct(uint64_t n,
                                                      uint64_t _res) {
  return div2_rect<std::function<FunctionVernac::R_div2(uint64_t)>>(
      [](uint64_t y) -> std::function<FunctionVernac::R_div2(uint64_t)> {
        return [=](uint64_t) mutable { return R_div2::r_div2_0(y); };
      },
      [](uint64_t y) -> std::function<FunctionVernac::R_div2(uint64_t)> {
        return [=](uint64_t) mutable { return R_div2::r_div2_1(y); };
      },
      [](uint64_t y, uint64_t y0,
         std::function<FunctionVernac::R_div2(uint64_t)> y2)
          -> std::function<FunctionVernac::R_div2(uint64_t)> {
        return [=](uint64_t) mutable {
          return R_div2::r_div2_2(y, y0, div2(y0), y2(div2(y0)));
        };
      },
      n)(_res);
}

Sig<uint64_t> FunctionVernac::list_sum_terminate(const List<uint64_t> &l) {
  if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
    return Sig<uint64_t>::exist(UINT64_C(0));
  } else {
    const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
    const auto &_sv0 = list_sum_terminate(*a1);
    const auto &[x0] = _sv0;
    return Sig<uint64_t>::exist((a0 + x0));
  }
}

uint64_t FunctionVernac::list_sum(const List<uint64_t> &l) {
  const auto &_sv = list_sum_terminate(l);
  const auto &[x] = _sv;
  return x;
}

FunctionVernac::R_list_sum
FunctionVernac::R_list_sum_correct(const List<uint64_t> &l, uint64_t _res) {
  return list_sum_rect<std::function<FunctionVernac::R_list_sum(uint64_t)>>(
      [](List<uint64_t> y)
          -> std::function<FunctionVernac::R_list_sum(uint64_t)> {
        return [=](uint64_t) mutable { return R_list_sum::r_list_sum_0(y); };
      },
      [](List<uint64_t> y, uint64_t y0, List<uint64_t> y1,
         std::function<FunctionVernac::R_list_sum(uint64_t)> y3)
          -> std::function<FunctionVernac::R_list_sum(uint64_t)> {
        return [=](uint64_t) mutable {
          return R_list_sum::r_list_sum_1(y, y0, y1, list_sum(y1),
                                          y3(list_sum(y1)));
        };
      },
      l)(_res);
}
