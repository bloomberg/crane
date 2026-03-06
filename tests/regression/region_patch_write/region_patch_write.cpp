#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <region_patch_write.h>
#include <stdexcept>
#include <string>
#include <variant>

std::shared_ptr<List<unsigned int>>
RegionPatchWrite::update_region(const std::shared_ptr<List<unsigned int>> &rom,
                                const unsigned int base,
                                std::shared_ptr<List<unsigned int>> bytes) {
  return std::visit(
      Overloaded{
          [](const typename List<unsigned int>::nil _args)
              -> std::shared_ptr<List<unsigned int>> {
            return List<unsigned int>::ctor::nil_();
          },
          [&](const typename List<unsigned int>::cons _args)
              -> std::shared_ptr<List<unsigned int>> {
            unsigned int r = _args._a0;
            std::shared_ptr<List<unsigned int>> rom_ = _args._a1;
            if (base <= 0) {
              return [&](void) {
                if (std::move(bytes).use_count() == 1 &&
                    std::move(bytes)->v().index() == 1) {
                  auto &_rf = std::get<1>(std::move(bytes)->v_mut());
                  unsigned int b = std::move(_rf._a0);
                  std::shared_ptr<List<unsigned int>> bytes_ =
                      std::move(_rf._a1);
                  _rf._a0 = std::move(b);
                  _rf._a1 =
                      update_region(std::move(rom_), 0, std::move(bytes_));
                  return std::move(bytes);
                } else {
                  return std::visit(
                      Overloaded{
                          [&](const typename List<unsigned int>::nil _args)
                              -> std::shared_ptr<List<unsigned int>> {
                            return List<unsigned int>::ctor::cons_(
                                std::move(r), std::move(rom_));
                          },
                          [&](const typename List<unsigned int>::cons _args)
                              -> std::shared_ptr<List<unsigned int>> {
                            unsigned int b = _args._a0;
                            std::shared_ptr<List<unsigned int>> bytes_ =
                                _args._a1;
                            return List<unsigned int>::ctor::cons_(
                                std::move(b), update_region(std::move(rom_), 0,
                                                            std::move(bytes_)));
                          }},
                      std::move(bytes)->v());
                }
              }();
            } else {
              unsigned int n = base - 1;
              return List<unsigned int>::ctor::cons_(
                  std::move(r),
                  update_region(std::move(rom_), std::move(n), bytes));
            }
          }},
      rom->v());
}
