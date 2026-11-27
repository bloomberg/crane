#pragma once

#include "crane_fn.h"
#include "crane_variant.h"
#include "fn.h"
#include "lazy.h"
#include "obj.h"
#include "shared_block.h"
#include "shared_variant.h"
#include <cstdint>
#include <memory>
#include <optional>
#include <stdexcept>
#include <utility>

struct LazyDirectLayer {
  template <typename tree> struct treeF {
    // TYPES
    struct RetF {
      uint64_t r;
    };

    struct TauF {
      tree t;
    };

    struct VisF {
      uint64_t e;
      crane::fn<tree(uint64_t)> k;
    };

    struct StopF {};

    using variant_t = crane::shared_variant<RetF, TauF, VisF, StopF>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    treeF() {}

    explicit treeF(RetF _v) : v_(std::move(_v)) {}

    explicit treeF(TauF _v) : v_(std::move(_v)) {}

    explicit treeF(VisF _v) : v_(std::move(_v)) {}

    explicit treeF(StopF _v) : v_(_v) {}

    template <typename CraneU>
    treeF(const treeF<CraneU> &_other)
        : v_([&]() -> variant_t {
            if (crane::holds_alternative<typename treeF<CraneU>::RetF>(
                    _other.v())) {
              const auto &[r] =
                  crane::get<typename treeF<CraneU>::RetF>(_other.v());
              return RetF{r};
            } else if (crane::holds_alternative<typename treeF<CraneU>::TauF>(
                           _other.v())) {
              const auto &[t] =
                  crane::get<typename treeF<CraneU>::TauF>(_other.v());
              return TauF{[&]() -> tree {
                if constexpr (crane_convertible<tree, const CraneU &>) {
                  return crane_convert<tree>(t);
                } else {
                  throw std::logic_error("unreachable: inactive constructor "
                                         "field at this instantiation");
                }
              }()};
            } else if (crane::holds_alternative<typename treeF<CraneU>::VisF>(
                           _other.v())) {
              const auto &[e, k] =
                  crane::get<typename treeF<CraneU>::VisF>(_other.v());
              return VisF{e, crane_convert<crane::fn<tree(uint64_t)>>(k)};
            } else {
              return StopF{};
            }
          }()) {}

    static treeF<tree> retf(uint64_t r) { return treeF<tree>(RetF{r}); }

    static treeF<tree> tauf(tree t) { return treeF<tree>(TauF{std::move(t)}); }

    static treeF<tree> visf(uint64_t e, crane::fn<tree(uint64_t)> k) {
      return treeF<tree>(VisF{e, std::move(k)});
    }

    static treeF<tree> stopf() { return treeF<tree>(StopF{}); }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  struct tree {
    // TYPES
    template <typename CraneS0 = tree> struct Go_ {
      treeF<CraneS0> observe;
    };

    using Go = Go_<>;
    using variant_t = crane::variant<Go>;

  private:
    // DATA
    crane::lazy<variant_t> lazy_v_;

  public:
    // CREATORS
    tree() {}

    explicit tree(Go _v)
        : lazy_v_(crane::lazy<variant_t>(variant_t(std::move(_v)))) {}

    explicit tree(crane::fn<variant_t()> _thunk)
        : lazy_v_(crane::lazy<variant_t>(std::move(_thunk))) {}

    static tree go(treeF<tree> observe) {
      return tree(crane::lazy<variant_t>(std::in_place, std::in_place_index<0>,
                                         std::move(observe)));
    }

    explicit tree(crane::lazy<variant_t> _cell) : lazy_v_(std::move(_cell)) {}

    template <typename F> static tree lazy_(F &&thunk) {
      return tree(crane::lazy<variant_t>::delegate(std::forward<F>(thunk)));
    }

    // ACCESSORS
    const variant_t &v() const { return lazy_v_.force(); }

    const crane::lazy<variant_t> &lazy_cell() const { return lazy_v_; }
  };

  static treeF<tree> observe(const tree &t);
  static tree Ret(uint64_t n);
  static tree Tau(const tree &t);
  static tree Vis(uint64_t e, const crane::fn<tree(uint64_t)> &k);
  static inline const tree Stop =
      crane::immortal(tree::go(treeF<tree>::stopf()));
  static tree taus(uint64_t n, uint64_t r);
  static tree ask(uint64_t n, uint64_t acc);
  /// The tree t runs to, answering every event with e + 1, within fuel
  /// steps.
  static std::optional<uint64_t> run(uint64_t fuel, const tree &t);
};
