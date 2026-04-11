#include <region_patch_write.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

std::shared_ptr<List<unsigned int>>
RegionPatchWrite::update_region(const std::shared_ptr<List<unsigned int>> &rom,
                                const unsigned int base,
                                std::shared_ptr<List<unsigned int>> bytes) {
  return std::visit(
      Overloaded{
          [](const typename List<unsigned int>::Nil)
              -> std::shared_ptr<List<unsigned int>> {
            return List<unsigned int>::nil();
          },
          [&](const typename List<unsigned int>::Cons _args)
              -> std::shared_ptr<List<unsigned int>> {
            if (base <= 0) {
              if (bytes.use_count() == 1 && bytes->v().index() == 1) {
                auto &_rf = std::get<1>(bytes->v_mut());
                unsigned int b = std::move(_rf.d_a0);
                std::shared_ptr<List<unsigned int>> bytes_ =
                    std::move(_rf.d_a1);
                _rf.d_a0 = b;
                _rf.d_a1 = update_region(std::move(_args.d_a1), 0u, bytes_);
                return bytes;
              } else {
                return std::visit(
                    Overloaded{
                        [&](const typename List<unsigned int>::Nil)
                            -> std::shared_ptr<List<unsigned int>> {
                          return List<unsigned int>::cons(_args.d_a0,
                                                          _args.d_a1);
                        },
                        [&](const typename List<unsigned int>::Cons _args0)
                            -> std::shared_ptr<List<unsigned int>> {
                          return List<unsigned int>::cons(
                              _args0.d_a0,
                              update_region(_args.d_a1, 0u, _args0.d_a1));
                        }},
                    bytes->v());
              }
            } else {
              unsigned int n = base - 1;
              return List<unsigned int>::cons(
                  _args.d_a0, update_region(_args.d_a1, n, bytes));
            }
          }},
      rom->v());
}
