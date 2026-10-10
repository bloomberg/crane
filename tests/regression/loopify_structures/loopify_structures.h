#ifndef INCLUDED_LOOPIFY_STRUCTURES
#define INCLUDED_LOOPIFY_STRUCTURES

#include "crane_fn.h"
#include "obj.h"
#include "small_vector.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <optional>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

template <typename A> struct List;

template <typename A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    A a;
    std::shared_ptr<List<A>> l;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  List() {}

  explicit List(Nil _v) : v_(_v) {}

  explicit List(Cons _v) : v_(std::move(_v)) {}

  template <typename CraneU>
  List(const List<CraneU> &_other)
      : v_([&]() -> variant_t {
          if (std::holds_alternative<typename List<CraneU>::Nil>(_other.v())) {
            return Nil{};
          } else {
            const auto &[a, l] =
                std::get<typename List<CraneU>::Cons>(_other.v());
            return Cons{
                [&]() -> A {
                  if constexpr (crane_convertible<A, const CraneU &>) {
                    return crane_convert<A>(a);
                  } else {
                    throw std::logic_error("unreachable: inactive constructor "
                                           "field at this instantiation");
                  }
                }(),
                (l ? std::make_shared<List<A>>(crane_convert<List<A>>(*l))
                   : nullptr)};
          }
        }()) {}

  static List<A> nil() { return List<A>(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List<A>(Cons{std::move(a), std::make_shared<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  ~List() {
    auto _next = [&](variant_t &_v) -> std::shared_ptr<List<A>> {
      if (auto *_alt = std::get_if<Cons>(&_v)) {
        if (_alt->l && _alt->l.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          return std::move(_alt->l);
        }
      }
      return nullptr;
    };
    std::shared_ptr<List<A>> _cur = _next(v_mut());
    while (_cur) {
      _cur = _next(_cur->v_mut());
    }
  }

  List(const List &) = default;
  List &operator=(const List &) = default;
  List(List &&) = default;
  List &operator=(List &&) = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  List<A> app(List<A> m) const {
    std::optional<List<A>> _root{};
    std::shared_ptr<List<A>> *_write = nullptr;
    const List<A> *_loop_self = this;
    List<A> _loop_m = std::move(m);
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
        auto _value = std::move(_loop_m);
        (_write ? *(*_write = std::make_shared<List<A>>(std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[a0, a1] = std::get<typename List<A>::Cons>(_sv.v());
        auto _cell = typename List<A>::Cons(a0, nullptr);
        List<A> &_node =
            (_write ? *(*_write = std::make_shared<List<A>>(std::move(_cell)))
                    : _root.emplace(std::move(_cell)));
        _write = &std::get<typename List<A>::Cons>(_node.v_mut()).l;
        _loop_self = crane_raw(a1);
        continue;
      }
    }
    return std::move(*_root);
  }
};

/// Nested and complex data structures.
struct LoopifyStructures {
  /// Nested list: elements or nested lists.
  struct nested {
    // TYPES
    struct Elem {
      uint64_t a0;
    };

    struct NList {
      std::shared_ptr<List<nested>> a0;
    };

    using variant_t = std::variant<Elem, NList>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    nested() {}

    explicit nested(Elem _v) : v_(std::move(_v)) {}

    explicit nested(NList _v) : v_(std::move(_v)) {}

    static nested elem(uint64_t a0) { return nested(Elem{a0}); }

    static nested nlist(List<nested> a0) {
      return nested(NList{std::make_shared<List<nested>>(std::move(a0))});
    }

    // MANIPULATORS
    ~nested() {
      if (std::holds_alternative<Elem>(v_mut())) {
        return;
      }
      crane::small_vector<std::shared_ptr<nested>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<NList>(&_v)) {
          if (_alt->a0 && _alt->a0.use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            auto _lp = _alt->a0.get();
            while (
                std::holds_alternative<typename List<nested>::Cons>(_lp->v())) {
              auto &_lc = std::get<typename List<nested>::Cons>(_lp->v_mut());
              _stack.push_back(std::make_shared<nested>(std::move(_lc.a)));
              if (_lc.l && _lc.l.use_count() == 1) {
                std::atomic_thread_fence(std::memory_order_acquire);
                _lp = _lc.l.get();
              } else {
                break;
              }
            }
            _alt->a0.reset();
          }
        }
      };
      _drain(v_mut());
      while (!_stack.empty()) {
        auto _cur = std::move(_stack.back());
        _stack.pop_back();
        if (_cur.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          _drain(_cur->v_mut());
        }
      }
    }

    nested(const nested &) = default;
    nested &operator=(const nested &) = default;
    nested(nested &&) = default;
    nested &operator=(nested &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    /// nested_flatten n flattens to a regular list.
    List<uint64_t> nested_flatten() const {
      if (std::holds_alternative<typename nested::Elem>(this->v())) {
        const auto &[a0] = std::get<typename nested::Elem>(this->v());
        return List<uint64_t>::cons(a0, List<uint64_t>::nil());
      } else {
        const auto &[a0] = std::get<typename nested::NList>(this->v());
        return flatten_nested_list_fuel(UINT64_C(1000), *a0);
      }
    }

    /// nested_depth n computes maximum nesting depth.
    uint64_t nested_depth() const {
      if (std::holds_alternative<typename nested::Elem>(this->v())) {
        return UINT64_C(0);
      } else {
        const auto &[a0] = std::get<typename nested::NList>(this->v());
        return (depth_nested_list_fuel(UINT64_C(1000), *a0) + 1);
      }
    }

    /// nested_sum n sums all elements in a nested structure.
    uint64_t nested_sum() const {
      if (std::holds_alternative<typename nested::Elem>(this->v())) {
        const auto &[a0] = std::get<typename nested::Elem>(this->v());
        return a0;
      } else {
        const auto &[a0] = std::get<typename nested::NList>(this->v());
        return sum_nested_list_fuel(UINT64_C(1000), *a0);
      }
    }

    template <typename T1, typename F0, typename F1>
    T1 nested_rec(F0 &&f, F1 &&f0) const {
      return this->template nested_rect<T1>(f, f0);
    }

    template <typename T1, typename F0, typename F1>
      requires std::is_invocable_r_v<T1, F0 &, const uint64_t &>
    T1 nested_rect(F0 &&f, F1 &&f0) const {
      if (std::holds_alternative<typename nested::Elem>(this->v())) {
        const auto &[a0] = std::get<typename nested::Elem>(this->v());
        return f(a0);
      } else {
        const auto &[a0] = std::get<typename nested::NList>(this->v());
        return f0(*a0);
      }
    }
  };

  /// Helper: sum all elements in a list of nested structures.
  /// Handles both tree and list levels in one function for full loopification.
  static uint64_t sum_nested_list_fuel(uint64_t fuel, const List<nested> &l);
  /// Helper: compute max depth among a list of nested structures.
  static uint64_t depth_nested_list_fuel(uint64_t fuel, const List<nested> &l);
  /// Helper: flatten a list of nested structures to a flat list of nats.
  static List<uint64_t> flatten_nested_list_fuel(uint64_t fuel,
                                                 const List<nested> &l);

  /// Quadtree: leaf or 4-way branch.
  struct quadtree {
    // TYPES
    struct QLeaf {
      uint64_t a0;
    };

    struct Quad {
      std::shared_ptr<quadtree> a0;
      std::shared_ptr<quadtree> a1;
      std::shared_ptr<quadtree> a2;
      std::shared_ptr<quadtree> a3;
    };

    using variant_t = std::variant<QLeaf, Quad>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    quadtree() {}

    explicit quadtree(QLeaf _v) : v_(std::move(_v)) {}

    explicit quadtree(Quad _v) : v_(std::move(_v)) {}

    static quadtree qleaf(uint64_t a0) { return quadtree(QLeaf{a0}); }

    static quadtree quad(quadtree a0, quadtree a1, quadtree a2, quadtree a3) {
      return quadtree(Quad{std::make_shared<quadtree>(std::move(a0)),
                           std::make_shared<quadtree>(std::move(a1)),
                           std::make_shared<quadtree>(std::move(a2)),
                           std::make_shared<quadtree>(std::move(a3))});
    }

    // MANIPULATORS
    ~quadtree() {
      if (std::holds_alternative<QLeaf>(v_mut())) {
        return;
      }
      if (auto *_alt = std::get_if<Quad>(&v_mut())) {
        if (!((_alt->a0 && _alt->a0.use_count() == 1) ||
              (_alt->a1 && _alt->a1.use_count() == 1) ||
              (_alt->a2 && _alt->a2.use_count() == 1) ||
              (_alt->a3 && _alt->a3.use_count() == 1))) {
          return;
        }
      }
      crane::small_vector<std::shared_ptr<quadtree>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<Quad>(&_v)) {
          if (_alt->a0 && _alt->a0.use_count() == 1) {
            _stack.push_back(std::move(_alt->a0));
          }
          if (_alt->a1 && _alt->a1.use_count() == 1) {
            _stack.push_back(std::move(_alt->a1));
          }
          if (_alt->a2 && _alt->a2.use_count() == 1) {
            _stack.push_back(std::move(_alt->a2));
          }
          if (_alt->a3 && _alt->a3.use_count() == 1) {
            _stack.push_back(std::move(_alt->a3));
          }
        }
      };
      _drain(v_mut());
      while (!_stack.empty()) {
        auto _cur = std::move(_stack.back());
        _stack.pop_back();
        if (_cur.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          _drain(_cur->v_mut());
        }
      }
    }

    quadtree(const quadtree &) = default;
    quadtree &operator=(const quadtree &) = default;
    quadtree(quadtree &&) = default;
    quadtree &operator=(quadtree &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    /// quad_map f t applies function to all leaves.
    template <typename F0>
      requires std::is_invocable_r_v<uint64_t, F0 &, const uint64_t &>
    quadtree quad_map(F0 &&f) const {
      const quadtree *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const quadtree *_self;
      };

      /// CraneCont_Quad: saves [a1, a2, a3], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Quad {
        std::shared_ptr<quadtree> a1;
        std::shared_ptr<quadtree> a2;
        std::shared_ptr<quadtree> a3;
      };

      /// CraneCont_Quad_1: saves [_tmp4, a2, a3], resumes after recursive call,
      /// then processes rest.
      struct CraneCont_Quad_1 {
        quadtree _tmp4;
        std::shared_ptr<quadtree> a2;
        std::shared_ptr<quadtree> a3;
      };

      /// CraneCont_Quad_2: saves [_tmp3, _tmp4, a3], resumes after recursive
      /// call, then processes rest.
      struct CraneCont_Quad_2 {
        quadtree _tmp3;
        quadtree _tmp4;
        std::shared_ptr<quadtree> a3;
      };

      /// CraneCont_Quad_3: saves [_tmp2, _tmp3, _tmp4], resumes after recursive
      /// call, then processes rest.
      struct CraneCont_Quad_3 {
        quadtree _tmp2;
        quadtree _tmp3;
        quadtree _tmp4;
      };

      using CraneFrame =
          std::variant<CraneEnter, CraneCont_Quad, CraneCont_Quad_1,
                       CraneCont_Quad_2, CraneCont_Quad_3>;
      quadtree _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified quad_map: CraneEnter -> CraneCont_Quad -> CraneCont_Quad_1
      /// -> CraneCont_Quad_2 -> CraneCont_Quad_3.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const quadtree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename quadtree::QLeaf>(_sv.v())) {
            const auto &[a0] = std::get<typename quadtree::QLeaf>(_sv.v());
            _result = quadtree::qleaf(f(a0));
          } else {
            const auto &[a0, a1, a2, a3] =
                std::get<typename quadtree::Quad>(_sv.v());
            _stack.emplace_back(CraneCont_Quad{a1, a2, a3});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          }
        } else if (std::holds_alternative<CraneCont_Quad>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Quad>(_frame));
          std::shared_ptr<quadtree> a1 = std::move(_f.a1);
          std::shared_ptr<quadtree> a2 = std::move(_f.a2);
          std::shared_ptr<quadtree> a3 = std::move(_f.a3);
          _stack.emplace_back(CraneCont_Quad_1{std::move(_result),
                                               std::move(a2), std::move(a3)});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        } else if (std::holds_alternative<CraneCont_Quad_1>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Quad_1>(_frame));
          std::shared_ptr<quadtree> a2 = std::move(_f.a2);
          std::shared_ptr<quadtree> a3 = std::move(_f.a3);
          _stack.emplace_back(CraneCont_Quad_2{
              std::move(_result), std::move(_f._tmp4), std::move(a3)});
          _stack.emplace_back(CraneEnter{crane_raw(a2)});
        } else if (std::holds_alternative<CraneCont_Quad_2>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Quad_2>(_frame));
          std::shared_ptr<quadtree> a3 = std::move(_f.a3);
          _stack.emplace_back(CraneCont_Quad_3{
              std::move(_result), std::move(_f._tmp3), std::move(_f._tmp4)});
          _stack.emplace_back(CraneEnter{crane_raw(a3)});
        } else {
          auto _f = std::move(std::get<CraneCont_Quad_3>(_frame));
          _result = quadtree::quad(std::move(_f._tmp4), std::move(_f._tmp3),
                                   std::move(_f._tmp2), std::move(_result));
        }
      }
      return _result;
    }

    /// quad_depth t computes quadtree depth.
    uint64_t quad_depth() const {
      const quadtree *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const quadtree *_self;
      };

      /// CraneCont_Quad: saves [a1, a2, a3], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Quad {
        std::shared_ptr<quadtree> a1;
        std::shared_ptr<quadtree> a2;
        std::shared_ptr<quadtree> a3;
      };

      /// CraneCont_Quad_1: saves [a2, a3, d1], resumes after recursive call,
      /// then processes rest.
      struct CraneCont_Quad_1 {
        std::shared_ptr<quadtree> a2;
        std::shared_ptr<quadtree> a3;
        uint64_t d1;
      };

      /// CraneCont_Quad_2: saves [a3, d1, d2], resumes after recursive call,
      /// then processes rest.
      struct CraneCont_Quad_2 {
        std::shared_ptr<quadtree> a3;
        uint64_t d1;
        uint64_t d2;
      };

      /// CraneCont_Quad_3: saves [d1, d2, d3], resumes after recursive call,
      /// then processes rest.
      struct CraneCont_Quad_3 {
        uint64_t d1;
        uint64_t d2;
        uint64_t d3;
      };

      using CraneFrame =
          std::variant<CraneEnter, CraneCont_Quad, CraneCont_Quad_1,
                       CraneCont_Quad_2, CraneCont_Quad_3>;
      uint64_t _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified quad_depth: CraneEnter -> CraneCont_Quad -> CraneCont_Quad_1
      /// -> CraneCont_Quad_2 -> CraneCont_Quad_3.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const quadtree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename quadtree::QLeaf>(_sv.v())) {
            _result = UINT64_C(0);
          } else {
            const auto &[a0, a1, a2, a3] =
                std::get<typename quadtree::Quad>(_sv.v());
            _stack.emplace_back(CraneCont_Quad{a1, a2, a3});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          }
        } else if (std::holds_alternative<CraneCont_Quad>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Quad>(_frame));
          std::shared_ptr<quadtree> a1 = std::move(_f.a1);
          std::shared_ptr<quadtree> a2 = std::move(_f.a2);
          std::shared_ptr<quadtree> a3 = std::move(_f.a3);
          uint64_t d1 = std::move(_result);
          _stack.emplace_back(
              CraneCont_Quad_1{std::move(a2), std::move(a3), d1});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        } else if (std::holds_alternative<CraneCont_Quad_1>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Quad_1>(_frame));
          std::shared_ptr<quadtree> a2 = std::move(_f.a2);
          std::shared_ptr<quadtree> a3 = std::move(_f.a3);
          uint64_t d1 = _f.d1;
          uint64_t d2 = std::move(_result);
          _stack.emplace_back(CraneCont_Quad_2{std::move(a3), d1, d2});
          _stack.emplace_back(CraneEnter{crane_raw(a2)});
        } else if (std::holds_alternative<CraneCont_Quad_2>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Quad_2>(_frame));
          std::shared_ptr<quadtree> a3 = std::move(_f.a3);
          uint64_t d1 = _f.d1;
          uint64_t d2 = _f.d2;
          uint64_t d3 = std::move(_result);
          _stack.emplace_back(CraneCont_Quad_3{d1, d2, d3});
          _stack.emplace_back(CraneEnter{crane_raw(a3)});
        } else {
          auto _f = std::move(std::get<CraneCont_Quad_3>(_frame));
          uint64_t d1 = _f.d1;
          uint64_t d2 = _f.d2;
          uint64_t d3 = _f.d3;
          uint64_t d4 = std::move(_result);
          _result = ([&]() -> uint64_t {
            if ((d1 <= d2 ? d2 : d1) <= (d3 <= d4 ? d4 : d3)) {
              if (d3 <= d4) {
                return d4;
              } else {
                return d3;
              }
            } else {
              if (d1 <= d2) {
                return d2;
              } else {
                return d1;
              }
            }
          }() + 1);
        }
      }
      return _result;
    }

    /// quad_sum t sums all values in quadtree.
    uint64_t quad_sum() const {
      const quadtree *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const quadtree *_self;
      };

      /// CraneCont_Quad: saves [a1, a2, a3], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Quad {
        std::shared_ptr<quadtree> a1;
        std::shared_ptr<quadtree> a2;
        std::shared_ptr<quadtree> a3;
      };

      /// CraneCont_Quad_1: saves [_tmp4, a2, a3], resumes after recursive call,
      /// then processes rest.
      struct CraneCont_Quad_1 {
        uint64_t _tmp4;
        std::shared_ptr<quadtree> a2;
        std::shared_ptr<quadtree> a3;
      };

      /// CraneCont_Quad_2: saves [_tmp3, _tmp4, a3], resumes after recursive
      /// call, then processes rest.
      struct CraneCont_Quad_2 {
        uint64_t _tmp3;
        uint64_t _tmp4;
        std::shared_ptr<quadtree> a3;
      };

      /// CraneCont_Quad_3: saves [_tmp2, _tmp3, _tmp4], resumes after recursive
      /// call, then processes rest.
      struct CraneCont_Quad_3 {
        uint64_t _tmp2;
        uint64_t _tmp3;
        uint64_t _tmp4;
      };

      using CraneFrame =
          std::variant<CraneEnter, CraneCont_Quad, CraneCont_Quad_1,
                       CraneCont_Quad_2, CraneCont_Quad_3>;
      uint64_t _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified quad_sum: CraneEnter -> CraneCont_Quad -> CraneCont_Quad_1
      /// -> CraneCont_Quad_2 -> CraneCont_Quad_3.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const quadtree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename quadtree::QLeaf>(_sv.v())) {
            const auto &[a0] = std::get<typename quadtree::QLeaf>(_sv.v());
            _result = std::move(a0);
          } else {
            const auto &[a0, a1, a2, a3] =
                std::get<typename quadtree::Quad>(_sv.v());
            _stack.emplace_back(CraneCont_Quad{a1, a2, a3});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          }
        } else if (std::holds_alternative<CraneCont_Quad>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Quad>(_frame));
          std::shared_ptr<quadtree> a1 = std::move(_f.a1);
          std::shared_ptr<quadtree> a2 = std::move(_f.a2);
          std::shared_ptr<quadtree> a3 = std::move(_f.a3);
          _stack.emplace_back(CraneCont_Quad_1{std::move(_result),
                                               std::move(a2), std::move(a3)});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        } else if (std::holds_alternative<CraneCont_Quad_1>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Quad_1>(_frame));
          std::shared_ptr<quadtree> a2 = std::move(_f.a2);
          std::shared_ptr<quadtree> a3 = std::move(_f.a3);
          _stack.emplace_back(
              CraneCont_Quad_2{std::move(_result), _f._tmp4, std::move(a3)});
          _stack.emplace_back(CraneEnter{crane_raw(a2)});
        } else if (std::holds_alternative<CraneCont_Quad_2>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Quad_2>(_frame));
          std::shared_ptr<quadtree> a3 = std::move(_f.a3);
          _stack.emplace_back(
              CraneCont_Quad_3{std::move(_result), _f._tmp3, _f._tmp4});
          _stack.emplace_back(CraneEnter{crane_raw(a3)});
        } else {
          auto _f = std::move(std::get<CraneCont_Quad_3>(_frame));
          _result = (_f._tmp4 + (_f._tmp3 + (_f._tmp2 + std::move(_result))));
        }
      }
      return _result;
    }

    template <typename T1, typename F0, typename F1>
    T1 quadtree_rec(F0 &&f, F1 &&f0) const {
      return this->template quadtree_rect<T1>(f, f0);
    }

    template <typename T1, typename F0, typename F1>
      requires std::is_invocable_r_v<T1, F0 &, const uint64_t &>
    T1 quadtree_rect(F0 &&f, F1 &&f0) const {
      const quadtree *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const quadtree *_self;
      };

      /// CraneCont_Quad: saves [a0, a1, a2, a3], resumes after recursive call,
      /// then processes rest.
      struct CraneCont_Quad {
        std::shared_ptr<quadtree> a0;
        std::shared_ptr<quadtree> a1;
        std::shared_ptr<quadtree> a2;
        std::shared_ptr<quadtree> a3;
      };

      /// CraneCont_Quad_1: saves [_tmp4, a0, a1, a2, a3], resumes after
      /// recursive call, then processes rest.
      struct CraneCont_Quad_1 {
        T1 _tmp4;
        std::shared_ptr<quadtree> a0;
        std::shared_ptr<quadtree> a1;
        std::shared_ptr<quadtree> a2;
        std::shared_ptr<quadtree> a3;
      };

      /// CraneCont_Quad_2: saves [_tmp3, _tmp4, a0, a1, a2, a3], resumes after
      /// recursive call, then processes rest.
      struct CraneCont_Quad_2 {
        T1 _tmp3;
        T1 _tmp4;
        std::shared_ptr<quadtree> a0;
        std::shared_ptr<quadtree> a1;
        std::shared_ptr<quadtree> a2;
        std::shared_ptr<quadtree> a3;
      };

      /// CraneCont_Quad_3: saves [_tmp2, _tmp3, _tmp4, a0, a1, a2, a3], resumes
      /// after recursive call, then processes rest.
      struct CraneCont_Quad_3 {
        T1 _tmp2;
        T1 _tmp3;
        T1 _tmp4;
        std::shared_ptr<quadtree> a0;
        std::shared_ptr<quadtree> a1;
        std::shared_ptr<quadtree> a2;
        std::shared_ptr<quadtree> a3;
      };

      using CraneFrame =
          std::variant<CraneEnter, CraneCont_Quad, CraneCont_Quad_1,
                       CraneCont_Quad_2, CraneCont_Quad_3>;
      T1 _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified quadtree_rect: CraneEnter -> CraneCont_Quad ->
      /// CraneCont_Quad_1 -> CraneCont_Quad_2 -> CraneCont_Quad_3.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const quadtree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename quadtree::QLeaf>(_sv.v())) {
            const auto &[a0] = std::get<typename quadtree::QLeaf>(_sv.v());
            _result = f(a0);
          } else {
            const auto &[a0, a1, a2, a3] =
                std::get<typename quadtree::Quad>(_sv.v());
            _stack.emplace_back(CraneCont_Quad{a0, a1, a2, a3});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          }
        } else if (std::holds_alternative<CraneCont_Quad>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Quad>(_frame));
          std::shared_ptr<quadtree> a0 = std::move(_f.a0);
          std::shared_ptr<quadtree> a1 = std::move(_f.a1);
          std::shared_ptr<quadtree> a2 = std::move(_f.a2);
          std::shared_ptr<quadtree> a3 = std::move(_f.a3);
          _stack.emplace_back(CraneCont_Quad_1{std::move(_result),
                                               std::move(a0), a1, std::move(a2),
                                               std::move(a3)});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        } else if (std::holds_alternative<CraneCont_Quad_1>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Quad_1>(_frame));
          std::shared_ptr<quadtree> a0 = std::move(_f.a0);
          std::shared_ptr<quadtree> a1 = std::move(_f.a1);
          std::shared_ptr<quadtree> a2 = std::move(_f.a2);
          std::shared_ptr<quadtree> a3 = std::move(_f.a3);
          _stack.emplace_back(CraneCont_Quad_2{
              std::move(_result), std::move(_f._tmp4), std::move(a0),
              std::move(a1), a2, std::move(a3)});
          _stack.emplace_back(CraneEnter{crane_raw(a2)});
        } else if (std::holds_alternative<CraneCont_Quad_2>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Quad_2>(_frame));
          std::shared_ptr<quadtree> a0 = std::move(_f.a0);
          std::shared_ptr<quadtree> a1 = std::move(_f.a1);
          std::shared_ptr<quadtree> a2 = std::move(_f.a2);
          std::shared_ptr<quadtree> a3 = std::move(_f.a3);
          _stack.emplace_back(CraneCont_Quad_3{
              std::move(_result), std::move(_f._tmp3), std::move(_f._tmp4),
              std::move(a0), std::move(a1), std::move(a2), a3});
          _stack.emplace_back(CraneEnter{crane_raw(a3)});
        } else {
          auto _f = std::move(std::get<CraneCont_Quad_3>(_frame));
          std::shared_ptr<quadtree> a0 = std::move(_f.a0);
          std::shared_ptr<quadtree> a1 = std::move(_f.a1);
          std::shared_ptr<quadtree> a2 = std::move(_f.a2);
          std::shared_ptr<quadtree> a3 = std::move(_f.a3);
          _result = f0(*a0, std::move(_f._tmp4), *a1, std::move(_f._tmp3), *a2,
                       std::move(_f._tmp2), *a3, std::move(_result));
        }
      }
      return _result;
    }
  };

  /// find_opt p l finds first element satisfying predicate, returns option.
  template <typename F0>
  static std::optional<uint64_t> find_opt(F0 &&p, const List<uint64_t> &l) {
    const List<uint64_t> *_loop_l = &l;
    while (true) {
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
        return std::optional<uint64_t>();
      } else {
        const auto &[a0, a1] =
            std::get<typename List<uint64_t>::Cons>(_loop_l->v());
        if (p(a0)) {
          return std::make_optional<uint64_t>(a0);
        } else {
          _loop_l = crane_raw(a1);
        }
      }
    }
  }

  /// map_opt f l maps option-returning function and filters out Nones.
  template <typename F0>
    requires std::is_invocable_r_v<std::optional<uint64_t>, F0 &,
                                   const uint64_t &>
  static List<uint64_t> map_opt(F0 &&f, const List<uint64_t> &l) {
    std::optional<List<uint64_t>> _root{};
    std::shared_ptr<List<uint64_t>> *_write = nullptr;
    const List<uint64_t> *_loop_l = &l;
    while (true) {
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
        auto _value = List<uint64_t>::nil();
        (_write
             ? *(*_write = std::make_shared<List<uint64_t>>(std::move(_value)))
             : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[a0, a1] =
            std::get<typename List<uint64_t>::Cons>(_loop_l->v());
        auto _cs = f(a0);
        if (_cs.has_value()) {
          const uint64_t &y = *_cs;
          auto _cell = typename List<uint64_t>::Cons(y, nullptr);
          List<uint64_t> &_node =
              (_write ? *(*_write = std::make_shared<List<uint64_t>>(
                              std::move(_cell)))
                      : _root.emplace(std::move(_cell)));
          _write = &std::get<typename List<uint64_t>::Cons>(_node.v_mut()).l;
          _loop_l = crane_raw(a1);
          continue;
        } else {
          _loop_l = crane_raw(a1);
          continue;
        }
      }
    }
    return std::move(*_root);
  }

  /// filter_map p f l filters and maps in one pass.
  template <typename F0, typename F1>
  static List<uint64_t> filter_map(F0 &&p, F1 &&f, const List<uint64_t> &l) {
    std::optional<List<uint64_t>> _root{};
    std::shared_ptr<List<uint64_t>> *_write = nullptr;
    const List<uint64_t> *_loop_l = &l;
    while (true) {
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
        auto _value = List<uint64_t>::nil();
        (_write
             ? *(*_write = std::make_shared<List<uint64_t>>(std::move(_value)))
             : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[a0, a1] =
            std::get<typename List<uint64_t>::Cons>(_loop_l->v());
        if (p(a0)) {
          auto _cell = typename List<uint64_t>::Cons(f(a0), nullptr);
          List<uint64_t> &_node =
              (_write ? *(*_write = std::make_shared<List<uint64_t>>(
                              std::move(_cell)))
                      : _root.emplace(std::move(_cell)));
          _write = &std::get<typename List<uint64_t>::Cons>(_node.v_mut()).l;
          _loop_l = crane_raw(a1);
          continue;
        } else {
          _loop_l = crane_raw(a1);
          continue;
        }
      }
    }
    return std::move(*_root);
  }

  /// find_first_some l finds first Some value in list of options.
  static std::optional<uint64_t>
  find_first_some(const List<std::optional<uint64_t>> &l);

  /// Tree type with values in leaves.
  struct ltree {
    // TYPES
    struct LLeaf {
      uint64_t a0;
    };

    struct LNode {
      uint64_t a0;
      std::shared_ptr<ltree> a1;
      std::shared_ptr<ltree> a2;
    };

    using variant_t = std::variant<LLeaf, LNode>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    ltree() {}

    explicit ltree(LLeaf _v) : v_(std::move(_v)) {}

    explicit ltree(LNode _v) : v_(std::move(_v)) {}

    static ltree lleaf(uint64_t a0) { return ltree(LLeaf{a0}); }

    static ltree lnode(uint64_t a0, ltree a1, ltree a2) {
      return ltree(LNode{a0, std::make_shared<ltree>(std::move(a1)),
                         std::make_shared<ltree>(std::move(a2))});
    }

    // MANIPULATORS
    ~ltree() {
      if (std::holds_alternative<LLeaf>(v_mut())) {
        return;
      }
      if (auto *_alt = std::get_if<LNode>(&v_mut())) {
        if (!((_alt->a1 && _alt->a1.use_count() == 1) ||
              (_alt->a2 && _alt->a2.use_count() == 1))) {
          return;
        }
      }
      crane::small_vector<std::shared_ptr<ltree>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<LNode>(&_v)) {
          if (_alt->a1 && _alt->a1.use_count() == 1) {
            _stack.push_back(std::move(_alt->a1));
          }
          if (_alt->a2 && _alt->a2.use_count() == 1) {
            _stack.push_back(std::move(_alt->a2));
          }
        }
      };
      _drain(v_mut());
      while (!_stack.empty()) {
        auto _cur = std::move(_stack.back());
        _stack.pop_back();
        if (_cur.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          _drain(_cur->v_mut());
        }
      }
    }

    ltree(const ltree &) = default;
    ltree &operator=(const ltree &) = default;
    ltree(ltree &&) = default;
    ltree &operator=(ltree &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    /// ltree_max t1 t2 element-wise max of two leaf-trees.
    ltree ltree_max(const ltree &t2) const {
      const ltree *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const ltree *_self;
        const ltree *t2;
      };

      /// CraneCont_LNode: saves [a2, a20, max_val], resumes after recursive
      /// call, then processes rest.
      struct CraneCont_LNode {
        std::shared_ptr<ltree> a2;
        const ltree *a20;
        uint64_t max_val;
      };

      /// CraneCont_LNode_1: saves [_tmp2, max_val], resumes after recursive
      /// call, then processes rest.
      struct CraneCont_LNode_1 {
        ltree _tmp2;
        uint64_t max_val;
      };

      using CraneFrame =
          std::variant<CraneEnter, CraneCont_LNode, CraneCont_LNode_1>;
      ltree _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self, &t2});
      /// Loopified ltree_max: CraneEnter -> CraneCont_LNode ->
      /// CraneCont_LNode_1.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const ltree *_self = _f._self;
          const ltree &t2 = *_f.t2;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename ltree::LLeaf>(_sv.v())) {
            const auto &[a0] = std::get<typename ltree::LLeaf>(_sv.v());
            if (std::holds_alternative<typename ltree::LLeaf>(t2.v())) {
              const auto &[a00] = std::get<typename ltree::LLeaf>(t2.v());
              _result = ltree::lleaf((a0 <= a00 ? a00 : a0));
            } else {
              _result = std::move(t2);
            }
          } else {
            const auto &[a0, a1, a2] = std::get<typename ltree::LNode>(_sv.v());
            if (std::holds_alternative<typename ltree::LLeaf>(t2.v())) {
              _result = *_self;
            } else {
              const auto &[a00, a10, a20] =
                  std::get<typename ltree::LNode>(t2.v());
              uint64_t max_val;
              if (a0 <= a00) {
                max_val = a00;
              } else {
                max_val = a0;
              }
              _stack.emplace_back(CraneCont_LNode{a2, crane_raw(a20), max_val});
              _stack.emplace_back(CraneEnter{crane_raw(a1), crane_raw(a10)});
            }
          }
        } else if (std::holds_alternative<CraneCont_LNode>(_frame)) {
          auto _f = std::move(std::get<CraneCont_LNode>(_frame));
          std::shared_ptr<ltree> a2 = std::move(_f.a2);
          const ltree &a20 = *_f.a20;
          uint64_t max_val = _f.max_val;
          _stack.emplace_back(CraneCont_LNode_1{std::move(_result), max_val});
          _stack.emplace_back(CraneEnter{crane_raw(a2), &a20});
        } else {
          auto _f = std::move(std::get<CraneCont_LNode_1>(_frame));
          uint64_t max_val = _f.max_val;
          _result =
              ltree::lnode(max_val, std::move(_f._tmp2), std::move(_result));
        }
      }
      return _result;
    }

    template <typename T1, typename F0, typename F1>
    T1 ltree_rec(F0 &&f, F1 &&f0) const {
      return this->template ltree_rect<T1>(f, f0);
    }

    template <typename T1, typename F0, typename F1>
      requires std::is_invocable_r_v<T1, F0 &, const uint64_t &>
    T1 ltree_rect(F0 &&f, F1 &&f0) const {
      const ltree *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const ltree *_self;
      };

      /// CraneCont_LNode: saves [a0, a1, a2], resumes after recursive call,
      /// then processes rest.
      struct CraneCont_LNode {
        uint64_t a0;
        std::shared_ptr<ltree> a1;
        std::shared_ptr<ltree> a2;
      };

      /// CraneCont_LNode_1: saves [_tmp2, a0, a1, a2], resumes after recursive
      /// call, then processes rest.
      struct CraneCont_LNode_1 {
        T1 _tmp2;
        uint64_t a0;
        std::shared_ptr<ltree> a1;
        std::shared_ptr<ltree> a2;
      };

      using CraneFrame =
          std::variant<CraneEnter, CraneCont_LNode, CraneCont_LNode_1>;
      T1 _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified ltree_rect: CraneEnter -> CraneCont_LNode ->
      /// CraneCont_LNode_1.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const ltree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename ltree::LLeaf>(_sv.v())) {
            const auto &[a0] = std::get<typename ltree::LLeaf>(_sv.v());
            _result = f(a0);
          } else {
            const auto &[a0, a1, a2] = std::get<typename ltree::LNode>(_sv.v());
            _stack.emplace_back(CraneCont_LNode{a0, a1, a2});
            _stack.emplace_back(CraneEnter{crane_raw(a1)});
          }
        } else if (std::holds_alternative<CraneCont_LNode>(_frame)) {
          auto _f = std::move(std::get<CraneCont_LNode>(_frame));
          uint64_t a0 = _f.a0;
          std::shared_ptr<ltree> a1 = std::move(_f.a1);
          std::shared_ptr<ltree> a2 = std::move(_f.a2);
          _stack.emplace_back(
              CraneCont_LNode_1{std::move(_result), a0, std::move(a1), a2});
          _stack.emplace_back(CraneEnter{crane_raw(a2)});
        } else {
          auto _f = std::move(std::get<CraneCont_LNode_1>(_frame));
          uint64_t a0 = _f.a0;
          std::shared_ptr<ltree> a1 = std::move(_f.a1);
          std::shared_ptr<ltree> a2 = std::move(_f.a2);
          _result = f0(a0, *a1, std::move(_f._tmp2), *a2, std::move(_result));
        }
      }
      return _result;
    }
  };
};

#endif // INCLUDED_LOOPIFY_STRUCTURES
