#include <function_vernac.h>

#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

std::shared_ptr<Sig<unsigned int>>
FunctionVernac::div2_terminate(const unsigned int n) {
  if (n <= 0) {
    return Sig<unsigned int>::exist(0u);
  } else {
    unsigned int n0 = n - 1;
    if (n0 <= 0) {
      return Sig<unsigned int>::exist(0u);
    } else {
      unsigned int n1 = n0 - 1;
      auto &&_sv = div2_terminate(n1);
      const auto &[d_x] = std::get<typename Sig<unsigned int>::Exist>(_sv->v());
      return Sig<unsigned int>::exist((d_x + 1));
    }
  }
}

__attribute__((pure)) unsigned int FunctionVernac::div2(const unsigned int n) {
  auto &&_sv = div2_terminate(n);
  const auto &[d_x] = std::get<typename Sig<unsigned int>::Exist>(_sv->v());
  return d_x;
}

std::shared_ptr<FunctionVernac::R_div2>
FunctionVernac::R_div2_correct(const unsigned int n, const unsigned int _res) {
  return div2_rect<
      std::function<std::shared_ptr<FunctionVernac::R_div2>(unsigned int)>>(
      [](const unsigned int y)
          -> std::function<std::shared_ptr<FunctionVernac::R_div2>(
              unsigned int)> {
        return [=](const unsigned int) mutable { return R_div2::r_div2_0(y); };
      },
      [](const unsigned int y)
          -> std::function<std::shared_ptr<FunctionVernac::R_div2>(
              unsigned int)> {
        return [=](const unsigned int) mutable { return R_div2::r_div2_1(y); };
      },
      [](const unsigned int y, const unsigned int y0,
         const std::function<std::shared_ptr<FunctionVernac::R_div2>(
             unsigned int)>
             y2)
          -> std::function<std::shared_ptr<FunctionVernac::R_div2>(
              unsigned int)> {
        return [=](const unsigned int) mutable {
          return R_div2::r_div2_2(y, y0, div2(y0), y2(div2(y0)));
        };
      },
      n)(_res);
}

std::shared_ptr<Sig<unsigned int>> FunctionVernac::list_sum_terminate(
    const std::shared_ptr<List<unsigned int>> &l) {
  if (std::holds_alternative<typename List<unsigned int>::Nil>(l->v())) {
    return Sig<unsigned int>::exist(0u);
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename List<unsigned int>::Cons>(l->v());
    auto &&_sv0 = list_sum_terminate(d_a1);
    const auto &[d_x0] = std::get<typename Sig<unsigned int>::Exist>(_sv0->v());
    return Sig<unsigned int>::exist((d_a0 + d_x0));
  }
}

__attribute__((pure)) unsigned int
FunctionVernac::list_sum(const std::shared_ptr<List<unsigned int>> &l) {
  auto &&_sv = list_sum_terminate(l);
  const auto &[d_x] = std::get<typename Sig<unsigned int>::Exist>(_sv->v());
  return d_x;
}

std::shared_ptr<FunctionVernac::R_list_sum>
FunctionVernac::R_list_sum_correct(const std::shared_ptr<List<unsigned int>> &l,
                                   const unsigned int _res) {
  return list_sum_rect<
      std::function<std::shared_ptr<FunctionVernac::R_list_sum>(unsigned int)>>(
      [](std::shared_ptr<List<unsigned int>> y)
          -> std::function<std::shared_ptr<FunctionVernac::R_list_sum>(
              unsigned int)> {
        return [=](const unsigned int) mutable {
          return R_list_sum::r_list_sum_0(y);
        };
      },
      [](std::shared_ptr<List<unsigned int>> y, const unsigned int y0,
         std::shared_ptr<List<unsigned int>> y1,
         const std::function<std::shared_ptr<FunctionVernac::R_list_sum>(
             unsigned int)>
             y3)
          -> std::function<std::shared_ptr<FunctionVernac::R_list_sum>(
              unsigned int)> {
        return [=](const unsigned int) mutable {
          return R_list_sum::r_list_sum_1(y, y0, y1, list_sum(y1),
                                          y3(list_sum(y1)));
        };
      },
      l)(_res);
}
