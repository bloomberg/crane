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
      return std::visit(
          Overloaded{
              [](const typename Sig<unsigned int>::Exist &_args) -> auto {
                return Sig<unsigned int>::exist((_args.d_x + 1));
              }},
          div2_terminate(n1)->v());
    }
  }
}

__attribute__((pure)) unsigned int FunctionVernac::div2(const unsigned int n) {
  return std::visit(
      Overloaded{[](const typename Sig<unsigned int>::Exist &_args)
                     -> unsigned int { return _args.d_x; }},
      div2_terminate(n)->v());
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
  return std::visit(
      Overloaded{
          [](const typename List<unsigned int>::Nil &)
              -> std::shared_ptr<Sig<unsigned int>> {
            return Sig<unsigned int>::exist(0u);
          },
          [](const typename List<unsigned int>::Cons &_args)
              -> std::shared_ptr<Sig<unsigned int>> {
            return std::visit(
                Overloaded{[&](const typename Sig<unsigned int>::Exist &_args0)
                               -> auto {
                  return Sig<unsigned int>::exist((_args.d_a0 + _args0.d_x));
                }},
                list_sum_terminate(_args.d_a1)->v());
          }},
      l->v());
}

__attribute__((pure)) unsigned int
FunctionVernac::list_sum(const std::shared_ptr<List<unsigned int>> &l) {
  return std::visit(
      Overloaded{[](const typename Sig<unsigned int>::Exist &_args)
                     -> unsigned int { return _args.d_x; }},
      list_sum_terminate(l)->v());
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
