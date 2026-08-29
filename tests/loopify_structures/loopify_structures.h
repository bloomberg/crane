#ifndef INCLUDED_LOOPIFY_STRUCTURES
#define INCLUDED_LOOPIFY_STRUCTURES

#include "crane_fn.h"
#include "small_vector.h"
#include <any>
#include <atomic>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

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

  template <typename _U> List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      this->v_ = Nil{};
    } else {
      const auto &[a, l] = std::get<typename List<_U>::Cons>(_other.v());
      this->v_ = Cons{
          [&]() -> A {
            if constexpr (std::is_same_v<_U, std::any>) {
              if (a.type() == typeid(A))
                return std::any_cast<A>(a);
              if constexpr (requires {
                              typename A::first_type;
                              typename A::second_type;
                            }) {
                const auto &[_k, _v] =
                    std::any_cast<std::pair<std::any, std::any>>(a);
                return A{[&]() -> typename A::first_type {
                           if constexpr (std::is_same_v<typename A::first_type,
                                                        std::any>)
                             return _k;
                           else
                             return std::any_cast<typename A::first_type>(_k);
                         }(),
                         [&]() -> typename A::second_type {
                           if constexpr (std::is_same_v<typename A::second_type,
                                                        std::any>)
                             return _v;
                           else
                             return std::any_cast<typename A::second_type>(_v);
                         }()};
              }
              return std::any_cast<A>(a);
            } else
              return A(a);
          }(),
          l ? std::make_shared<List<A>>(*l) : nullptr};
    }
  }

  static List<A> nil() { return List<A>(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List<A>(Cons{std::move(a), std::make_shared<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  ~List() {
    crane::small_vector<std::shared_ptr<List<A>>> _stack = {};
    auto _drain = [&](variant_t &_v) {
      if (auto *_alt = std::get_if<Cons>(&_v)) {
        if (_alt->l) {
          _stack.push_back(std::move(_alt->l));
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

  List(const List &) = default;
  List &operator=(const List &) = default;
  List(List &&) noexcept = default;
  List &operator=(List &&) noexcept = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  List<A> app(List<A> m) const {
    std::shared_ptr<List<A>> _head{};
    std::shared_ptr<List<A>> *_write = &_head;
    const List *_loop_self = this;
    List<A> _loop_m = std::move(m);
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
        *_write = std::make_shared<List<A>>(std::move(_loop_m));
        break;
      } else {
        const auto &[a0, a1] = std::get<typename List<A>::Cons>(_sv.v());
        auto _cell =
            std::make_shared<List<A>>(typename List<A>::Cons(a0, nullptr));
        *_write = std::move(_cell);
        _write = &std::get<typename List<A>::Cons>((*_write)->v_mut()).l;
        _loop_self = crane_raw(a1);
        continue;
      }
    }
    return std::move(*_head);
  }
};

struct LoopifyStructures {
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
      crane::small_vector<std::shared_ptr<nested>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<NList>(&_v)) {
          if (_alt->a0 && _alt->a0.use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            auto *_lp = _alt->a0.get();
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
    nested(nested &&) noexcept = default;
    nested &operator=(nested &&) noexcept = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    List<uint64_t> nested_flatten() const {
      if (std::holds_alternative<typename nested::Elem>(this->v())) {
        const auto &[a0] = std::get<typename nested::Elem>(this->v());
        return List<uint64_t>::cons(a0, List<uint64_t>::nil());
      } else {
        const auto &[a0] = std::get<typename nested::NList>(this->v());
        return flatten_nested_list_fuel(UINT64_C(1000), *a0);
      }
    }

    uint64_t nested_depth() const {
      if (std::holds_alternative<typename nested::Elem>(this->v())) {
        return UINT64_C(0);
      } else {
        const auto &[a0] = std::get<typename nested::NList>(this->v());
        return (depth_nested_list_fuel(UINT64_C(1000), *a0) + 1);
      }
    }

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
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F1 &, List<nested> &>
    T1 nested_rec(F0 &&f, F1 &&f0) const {
      if (std::holds_alternative<typename nested::Elem>(this->v())) {
        const auto &[a0] = std::get<typename nested::Elem>(this->v());
        return f(a0);
      } else {
        const auto &[a0] = std::get<typename nested::NList>(this->v());
        return f0(*a0);
      }
    }

    template <typename T1, typename F0, typename F1>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F1 &, List<nested> &>
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

  static uint64_t sum_nested_list_fuel(uint64_t fuel, const List<nested> &l);
  static uint64_t depth_nested_list_fuel(uint64_t fuel, const List<nested> &l);
  static List<uint64_t> flatten_nested_list_fuel(uint64_t fuel,
                                                 const List<nested> &l);

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
      crane::small_vector<std::shared_ptr<quadtree>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<Quad>(&_v)) {
          if (_alt->a0) {
            _stack.push_back(std::move(_alt->a0));
          }
          if (_alt->a1) {
            _stack.push_back(std::move(_alt->a1));
          }
          if (_alt->a2) {
            _stack.push_back(std::move(_alt->a2));
          }
          if (_alt->a3) {
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
    quadtree(quadtree &&) noexcept = default;
    quadtree &operator=(quadtree &&) noexcept = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    template <typename F0>
      requires std::is_invocable_r_v<uint64_t, F0 &, uint64_t &>
    quadtree quad_map(F0 &&f) const {
      const quadtree *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const quadtree *_self;
      };

      /// _After_Quad: saves [a2, a1, a0], dispatches next recursive call.
      struct _After_Quad {
        const quadtree *a2;
        const quadtree *a1;
        const quadtree *a0;
      };

      /// _After_Quad_1: saves [_result, a1, a0], dispatches next recursive
      /// call.
      struct _After_Quad_1 {
        quadtree _result;
        const quadtree *a1;
        const quadtree *a0;
      };

      /// _After_Quad_2: saves [_result_0, _result_1, a0], dispatches next
      /// recursive call.
      struct _After_Quad_2 {
        quadtree _result_0;
        quadtree _result_1;
        const quadtree *a0;
      };

      /// _Combine_Quad: receives partial results, combines with _result from
      /// final call.
      struct _Combine_Quad {
        quadtree _result_0;
        quadtree _result_1;
        quadtree _result_2;
      };

      using _Frame = std::variant<_Enter, _After_Quad, _After_Quad_1,
                                  _After_Quad_2, _Combine_Quad>;
      quadtree _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified quad_map: _Enter -> _After_Quad -> _After_Quad_1 ->
      /// _After_Quad_2 -> _Combine_Quad.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const quadtree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename quadtree::QLeaf>(_sv.v())) {
            const auto &[a0] = std::get<typename quadtree::QLeaf>(_sv.v());
            _result = quadtree::qleaf(f(a0));
          } else {
            const auto &[a0, a1, a2, a3] =
                std::get<typename quadtree::Quad>(_sv.v());
            _stack.emplace_back(
                _After_Quad{crane_raw(a2), crane_raw(a1), crane_raw(a0)});
            _stack.emplace_back(_Enter{crane_raw(a3)});
          }
        } else if (std::holds_alternative<_After_Quad>(_frame)) {
          auto _f = std::move(std::get<_After_Quad>(_frame));
          _stack.emplace_back(_After_Quad_1{std::move(_result), _f.a1, _f.a0});
          _stack.emplace_back(_Enter{_f.a2});
        } else if (std::holds_alternative<_After_Quad_1>(_frame)) {
          auto _f = std::move(std::get<_After_Quad_1>(_frame));
          _stack.emplace_back(
              _After_Quad_2{std::move(_f._result), std::move(_result), _f.a0});
          _stack.emplace_back(_Enter{_f.a1});
        } else if (std::holds_alternative<_After_Quad_2>(_frame)) {
          auto _f = std::move(std::get<_After_Quad_2>(_frame));
          _stack.emplace_back(_Combine_Quad{std::move(_f._result_0),
                                            std::move(_f._result_1),
                                            std::move(_result)});
          _stack.emplace_back(_Enter{_f.a0});
        } else {
          auto _f = std::move(std::get<_Combine_Quad>(_frame));
          _result =
              quadtree::quad(std::move(_result), std::move(_f._result_2),
                             std::move(_f._result_1), std::move(_f._result_0));
        }
      }
      return _result;
    }

    uint64_t quad_depth() const {
      const quadtree *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const quadtree *_self;
      };

      /// _Cont_Quad: saves [a1, a2, a3], resumes after recursive call, then
      /// processes rest.
      struct _Cont_Quad {
        std::shared_ptr<quadtree> a1;
        std::shared_ptr<quadtree> a2;
        std::shared_ptr<quadtree> a3;
      };

      /// _Cont_Quad_1: saves [a2, a3, d1], resumes after recursive call, then
      /// processes rest.
      struct _Cont_Quad_1 {
        std::shared_ptr<quadtree> a2;
        std::shared_ptr<quadtree> a3;
        uint64_t d1;
      };

      /// _Cont_Quad_2: saves [a3, d1, d2], resumes after recursive call, then
      /// processes rest.
      struct _Cont_Quad_2 {
        std::shared_ptr<quadtree> a3;
        uint64_t d1;
        uint64_t d2;
      };

      /// _Cont_Quad_3: saves [d1, d2, d3], resumes after recursive call, then
      /// processes rest.
      struct _Cont_Quad_3 {
        uint64_t d1;
        uint64_t d2;
        uint64_t d3;
      };

      using _Frame = std::variant<_Enter, _Cont_Quad, _Cont_Quad_1,
                                  _Cont_Quad_2, _Cont_Quad_3>;
      uint64_t _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified quad_depth: _Enter -> _Cont_Quad -> _Cont_Quad_1 ->
      /// _Cont_Quad_2 -> _Cont_Quad_3.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const quadtree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename quadtree::QLeaf>(_sv.v())) {
            _result = UINT64_C(0);
          } else {
            const auto &[a0, a1, a2, a3] =
                std::get<typename quadtree::Quad>(_sv.v());
            _stack.emplace_back(_Cont_Quad{a1, a2, a3});
            _stack.emplace_back(_Enter{crane_raw(a0)});
          }
        } else if (std::holds_alternative<_Cont_Quad>(_frame)) {
          auto _f = std::move(std::get<_Cont_Quad>(_frame));
          std::shared_ptr<quadtree> a1 = std::move(_f.a1);
          std::shared_ptr<quadtree> a2 = std::move(_f.a2);
          std::shared_ptr<quadtree> a3 = std::move(_f.a3);
          uint64_t d1 = std::move(_result);
          _stack.emplace_back(_Cont_Quad_1{std::move(a2), std::move(a3), d1});
          _stack.emplace_back(_Enter{crane_raw(a1)});
        } else if (std::holds_alternative<_Cont_Quad_1>(_frame)) {
          auto _f = std::move(std::get<_Cont_Quad_1>(_frame));
          std::shared_ptr<quadtree> a2 = std::move(_f.a2);
          std::shared_ptr<quadtree> a3 = std::move(_f.a3);
          uint64_t d1 = _f.d1;
          uint64_t d2 = std::move(_result);
          _stack.emplace_back(_Cont_Quad_2{std::move(a3), d1, d2});
          _stack.emplace_back(_Enter{crane_raw(a2)});
        } else if (std::holds_alternative<_Cont_Quad_2>(_frame)) {
          auto _f = std::move(std::get<_Cont_Quad_2>(_frame));
          std::shared_ptr<quadtree> a3 = std::move(_f.a3);
          uint64_t d1 = _f.d1;
          uint64_t d2 = _f.d2;
          uint64_t d3 = std::move(_result);
          _stack.emplace_back(_Cont_Quad_3{d1, d2, d3});
          _stack.emplace_back(_Enter{crane_raw(a3)});
        } else {
          auto _f = std::move(std::get<_Cont_Quad_3>(_frame));
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

    uint64_t quad_sum() const {
      const quadtree *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const quadtree *_self;
      };

      /// _After_Quad: saves [a2, a1, a0], dispatches next recursive call.
      struct _After_Quad {
        const quadtree *a2;
        const quadtree *a1;
        const quadtree *a0;
      };

      /// _After_Quad_1: saves [_result, a1, a0], dispatches next recursive
      /// call.
      struct _After_Quad_1 {
        uint64_t _result;
        const quadtree *a1;
        const quadtree *a0;
      };

      /// _After_Quad_2: saves [_result_0, _result_1, a0], dispatches next
      /// recursive call.
      struct _After_Quad_2 {
        uint64_t _result_0;
        uint64_t _result_1;
        const quadtree *a0;
      };

      /// _Combine_Quad: receives partial results, combines with _result from
      /// final call.
      struct _Combine_Quad {
        uint64_t _result_0;
        uint64_t _result_1;
        uint64_t _result_2;
      };

      using _Frame = std::variant<_Enter, _After_Quad, _After_Quad_1,
                                  _After_Quad_2, _Combine_Quad>;
      uint64_t _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified quad_sum: _Enter -> _After_Quad -> _After_Quad_1 ->
      /// _After_Quad_2 -> _Combine_Quad.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const quadtree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename quadtree::QLeaf>(_sv.v())) {
            const auto &[a0] = std::get<typename quadtree::QLeaf>(_sv.v());
            _result = std::move(a0);
          } else {
            const auto &[a0, a1, a2, a3] =
                std::get<typename quadtree::Quad>(_sv.v());
            _stack.emplace_back(
                _After_Quad{crane_raw(a2), crane_raw(a1), crane_raw(a0)});
            _stack.emplace_back(_Enter{crane_raw(a3)});
          }
        } else if (std::holds_alternative<_After_Quad>(_frame)) {
          auto _f = std::move(std::get<_After_Quad>(_frame));
          _stack.emplace_back(_After_Quad_1{std::move(_result), _f.a1, _f.a0});
          _stack.emplace_back(_Enter{_f.a2});
        } else if (std::holds_alternative<_After_Quad_1>(_frame)) {
          auto _f = std::move(std::get<_After_Quad_1>(_frame));
          _stack.emplace_back(
              _After_Quad_2{_f._result, std::move(_result), _f.a0});
          _stack.emplace_back(_Enter{_f.a1});
        } else if (std::holds_alternative<_After_Quad_2>(_frame)) {
          auto _f = std::move(std::get<_After_Quad_2>(_frame));
          _stack.emplace_back(
              _Combine_Quad{_f._result_0, _f._result_1, std::move(_result)});
          _stack.emplace_back(_Enter{_f.a0});
        } else {
          auto _f = std::move(std::get<_Combine_Quad>(_frame));
          _result = (std::move(_result) +
                     (_f._result_2 + (_f._result_1 + _f._result_0)));
        }
      }
      return _result;
    }

    template <typename T1, typename F0, typename F1>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F1 &, quadtree &, T1 &, quadtree &,
                                     T1 &, quadtree &, T1 &, quadtree &, T1 &>
    T1 quadtree_rec(F0 &&f, F1 &&f0) const {
      const quadtree *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const quadtree *_self;
      };

      /// _After_Quad: saves [a2_0, a1_0, a0_0, a3, a2_1, a1_1, a0_1],
      /// dispatches next recursive call.
      struct _After_Quad {
        const quadtree *a2_0;
        const quadtree *a1_0;
        const quadtree *a0_0;
        quadtree a3;
        quadtree a2_1;
        quadtree a1_1;
        quadtree a0_1;
      };

      /// _After_Quad_1: saves [_result, a1_0, a0_0, a3, a2, a1_1, a0_1],
      /// dispatches next recursive call.
      struct _After_Quad_1 {
        std::decay_t<T1> _result;
        const quadtree *a1_0;
        const quadtree *a0_0;
        quadtree a3;
        quadtree a2;
        quadtree a1_1;
        quadtree a0_1;
      };

      /// _After_Quad_2: saves [_result_0, _result_1, a0_0, a3, a2, a1, a0_1],
      /// dispatches next recursive call.
      struct _After_Quad_2 {
        std::decay_t<T1> _result_0;
        std::decay_t<T1> _result_1;
        const quadtree *a0_0;
        quadtree a3;
        quadtree a2;
        quadtree a1;
        quadtree a0_1;
      };

      /// _Combine_Quad: receives partial results, combines with _result from
      /// final call.
      struct _Combine_Quad {
        std::decay_t<T1> _result_0;
        std::decay_t<T1> _result_1;
        std::decay_t<T1> _result_2;
        quadtree a3;
        quadtree a2;
        quadtree a1;
        quadtree a0;
      };

      using _Frame = std::variant<_Enter, _After_Quad, _After_Quad_1,
                                  _After_Quad_2, _Combine_Quad>;
      T1 _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified quadtree_rec: _Enter -> _After_Quad -> _After_Quad_1 ->
      /// _After_Quad_2 -> _Combine_Quad.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const quadtree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename quadtree::QLeaf>(_sv.v())) {
            const auto &[a0] = std::get<typename quadtree::QLeaf>(_sv.v());
            _result = f(a0);
          } else {
            const auto &[a0, a1, a2, a3] =
                std::get<typename quadtree::Quad>(_sv.v());
            _stack.emplace_back(_After_Quad{crane_raw(a2), crane_raw(a1),
                                            crane_raw(a0), *a3, *a2, *a1, *a0});
            _stack.emplace_back(_Enter{crane_raw(a3)});
          }
        } else if (std::holds_alternative<_After_Quad>(_frame)) {
          auto _f = std::move(std::get<_After_Quad>(_frame));
          _stack.emplace_back(_After_Quad_1{
              std::move(_result), _f.a1_0, _f.a0_0, std::move(_f.a3),
              std::move(_f.a2_1), std::move(_f.a1_1), std::move(_f.a0_1)});
          _stack.emplace_back(_Enter{_f.a2_0});
        } else if (std::holds_alternative<_After_Quad_1>(_frame)) {
          auto _f = std::move(std::get<_After_Quad_1>(_frame));
          _stack.emplace_back(
              _After_Quad_2{std::move(_f._result), std::move(_result), _f.a0_0,
                            std::move(_f.a3), std::move(_f.a2),
                            std::move(_f.a1_1), std::move(_f.a0_1)});
          _stack.emplace_back(_Enter{_f.a1_0});
        } else if (std::holds_alternative<_After_Quad_2>(_frame)) {
          auto _f = std::move(std::get<_After_Quad_2>(_frame));
          _stack.emplace_back(_Combine_Quad{
              std::move(_f._result_0), std::move(_f._result_1),
              std::move(_result), std::move(_f.a3), std::move(_f.a2),
              std::move(_f.a1), std::move(_f.a0_1)});
          _stack.emplace_back(_Enter{_f.a0_0});
        } else {
          auto _f = std::move(std::get<_Combine_Quad>(_frame));
          _result = f0(std::move(_f.a0), std::move(_result), std::move(_f.a1),
                       std::move(_f._result_2), std::move(_f.a2),
                       std::move(_f._result_1), std::move(_f.a3),
                       std::move(_f._result_0));
        }
      }
      return _result;
    }

    template <typename T1, typename F0, typename F1>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F1 &, quadtree &, T1 &, quadtree &,
                                     T1 &, quadtree &, T1 &, quadtree &, T1 &>
    T1 quadtree_rect(F0 &&f, F1 &&f0) const {
      const quadtree *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const quadtree *_self;
      };

      /// _After_Quad: saves [a2_0, a1_0, a0_0, a3, a2_1, a1_1, a0_1],
      /// dispatches next recursive call.
      struct _After_Quad {
        const quadtree *a2_0;
        const quadtree *a1_0;
        const quadtree *a0_0;
        quadtree a3;
        quadtree a2_1;
        quadtree a1_1;
        quadtree a0_1;
      };

      /// _After_Quad_1: saves [_result, a1_0, a0_0, a3, a2, a1_1, a0_1],
      /// dispatches next recursive call.
      struct _After_Quad_1 {
        std::decay_t<T1> _result;
        const quadtree *a1_0;
        const quadtree *a0_0;
        quadtree a3;
        quadtree a2;
        quadtree a1_1;
        quadtree a0_1;
      };

      /// _After_Quad_2: saves [_result_0, _result_1, a0_0, a3, a2, a1, a0_1],
      /// dispatches next recursive call.
      struct _After_Quad_2 {
        std::decay_t<T1> _result_0;
        std::decay_t<T1> _result_1;
        const quadtree *a0_0;
        quadtree a3;
        quadtree a2;
        quadtree a1;
        quadtree a0_1;
      };

      /// _Combine_Quad: receives partial results, combines with _result from
      /// final call.
      struct _Combine_Quad {
        std::decay_t<T1> _result_0;
        std::decay_t<T1> _result_1;
        std::decay_t<T1> _result_2;
        quadtree a3;
        quadtree a2;
        quadtree a1;
        quadtree a0;
      };

      using _Frame = std::variant<_Enter, _After_Quad, _After_Quad_1,
                                  _After_Quad_2, _Combine_Quad>;
      T1 _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified quadtree_rect: _Enter -> _After_Quad -> _After_Quad_1 ->
      /// _After_Quad_2 -> _Combine_Quad.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const quadtree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename quadtree::QLeaf>(_sv.v())) {
            const auto &[a0] = std::get<typename quadtree::QLeaf>(_sv.v());
            _result = f(a0);
          } else {
            const auto &[a0, a1, a2, a3] =
                std::get<typename quadtree::Quad>(_sv.v());
            _stack.emplace_back(_After_Quad{crane_raw(a2), crane_raw(a1),
                                            crane_raw(a0), *a3, *a2, *a1, *a0});
            _stack.emplace_back(_Enter{crane_raw(a3)});
          }
        } else if (std::holds_alternative<_After_Quad>(_frame)) {
          auto _f = std::move(std::get<_After_Quad>(_frame));
          _stack.emplace_back(_After_Quad_1{
              std::move(_result), _f.a1_0, _f.a0_0, std::move(_f.a3),
              std::move(_f.a2_1), std::move(_f.a1_1), std::move(_f.a0_1)});
          _stack.emplace_back(_Enter{_f.a2_0});
        } else if (std::holds_alternative<_After_Quad_1>(_frame)) {
          auto _f = std::move(std::get<_After_Quad_1>(_frame));
          _stack.emplace_back(
              _After_Quad_2{std::move(_f._result), std::move(_result), _f.a0_0,
                            std::move(_f.a3), std::move(_f.a2),
                            std::move(_f.a1_1), std::move(_f.a0_1)});
          _stack.emplace_back(_Enter{_f.a1_0});
        } else if (std::holds_alternative<_After_Quad_2>(_frame)) {
          auto _f = std::move(std::get<_After_Quad_2>(_frame));
          _stack.emplace_back(_Combine_Quad{
              std::move(_f._result_0), std::move(_f._result_1),
              std::move(_result), std::move(_f.a3), std::move(_f.a2),
              std::move(_f.a1), std::move(_f.a0_1)});
          _stack.emplace_back(_Enter{_f.a0_0});
        } else {
          auto _f = std::move(std::get<_Combine_Quad>(_frame));
          _result = f0(std::move(_f.a0), std::move(_result), std::move(_f.a1),
                       std::move(_f._result_2), std::move(_f.a2),
                       std::move(_f._result_1), std::move(_f.a3),
                       std::move(_f._result_0));
        }
      }
      return _result;
    }
  };

  template <typename F0>
    requires std::is_invocable_r_v<bool, F0 &, uint64_t &>
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

  template <typename F0>
    requires std::is_invocable_r_v<std::optional<uint64_t>, F0 &, uint64_t &>
  static List<uint64_t> map_opt(F0 &&f, const List<uint64_t> &l) {
    std::shared_ptr<List<uint64_t>> _head{};
    std::shared_ptr<List<uint64_t>> *_write = &_head;
    const List<uint64_t> *_loop_l = &l;
    while (true) {
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
        *_write = std::make_shared<List<uint64_t>>(List<uint64_t>::nil());
        break;
      } else {
        const auto &[a0, a1] =
            std::get<typename List<uint64_t>::Cons>(_loop_l->v());
        auto _cs = f(a0);
        if (_cs.has_value()) {
          const uint64_t &y = *_cs;
          auto _cell = std::make_shared<List<uint64_t>>(
              typename List<uint64_t>::Cons(y, nullptr));
          *_write = std::move(_cell);
          _write =
              &std::get<typename List<uint64_t>::Cons>((*_write)->v_mut()).l;
          _loop_l = crane_raw(a1);
          continue;
        } else {
          _loop_l = crane_raw(a1);
          continue;
        }
      }
    }
    return std::move(*_head);
  }

  template <typename F0, typename F1>
    requires std::is_invocable_r_v<bool, F0 &, uint64_t &> &&
             std::is_invocable_r_v<uint64_t, F1 &, uint64_t &>
  static List<uint64_t> filter_map(F0 &&p, F1 &&f, const List<uint64_t> &l) {
    std::shared_ptr<List<uint64_t>> _head{};
    std::shared_ptr<List<uint64_t>> *_write = &_head;
    const List<uint64_t> *_loop_l = &l;
    while (true) {
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
        *_write = std::make_shared<List<uint64_t>>(List<uint64_t>::nil());
        break;
      } else {
        const auto &[a0, a1] =
            std::get<typename List<uint64_t>::Cons>(_loop_l->v());
        if (p(a0)) {
          auto _cell = std::make_shared<List<uint64_t>>(
              typename List<uint64_t>::Cons(f(a0), nullptr));
          *_write = std::move(_cell);
          _write =
              &std::get<typename List<uint64_t>::Cons>((*_write)->v_mut()).l;
          _loop_l = crane_raw(a1);
          continue;
        } else {
          _loop_l = crane_raw(a1);
          continue;
        }
      }
    }
    return std::move(*_head);
  }

  static std::optional<uint64_t>
  find_first_some(const List<std::optional<uint64_t>> &l);

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
      crane::small_vector<std::shared_ptr<ltree>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<LNode>(&_v)) {
          if (_alt->a1) {
            _stack.push_back(std::move(_alt->a1));
          }
          if (_alt->a2) {
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
    ltree(ltree &&) noexcept = default;
    ltree &operator=(ltree &&) noexcept = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    ltree ltree_max(ltree t2) const {
      const ltree *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const ltree *_self;
        ltree t2;
      };

      /// _After_LNode: saves [a1, a10, max_val], dispatches next recursive
      /// call.
      struct _After_LNode {
        ltree *a1;
        ltree a10;
        uint64_t max_val;
      };

      /// _Combine_LNode: receives partial results, combines with _result from
      /// final call.
      struct _Combine_LNode {
        ltree _result;
        uint64_t max_val;
      };

      using _Frame = std::variant<_Enter, _After_LNode, _Combine_LNode>;
      ltree _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self, std::move(t2)});
      /// Loopified ltree_max: _Enter -> _After_LNode -> _Combine_LNode.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const ltree *_self = _f._self;
          ltree t2 = std::move(_f.t2);
          auto &&_sv = *_self;
          if (std::holds_alternative<typename ltree::LLeaf>(_sv.v())) {
            const auto &[a0] = std::get<typename ltree::LLeaf>(_sv.v());
            if (std::holds_alternative<typename ltree::LLeaf>(t2.v_mut())) {
              auto &[a00] = std::get<typename ltree::LLeaf>(t2.v_mut());
              _result =
                  ltree::lleaf((a0 <= a00 ? std::move(a00) : std::move(a0)));
            } else {
              _result = std::move(t2);
            }
          } else {
            const auto &[a0, a1, a2] = std::get<typename ltree::LNode>(_sv.v());
            if (std::holds_alternative<typename ltree::LLeaf>(t2.v_mut())) {
              _result = *_self;
            } else {
              auto &[a00, a10, a20] =
                  std::get<typename ltree::LNode>(t2.v_mut());
              uint64_t max_val;
              if (a0 <= a00) {
                max_val = a00;
              } else {
                max_val = a0;
              }
              _stack.emplace_back(_After_LNode{crane_raw(a1), *a10, max_val});
              _stack.emplace_back(_Enter{crane_raw(a2), *a20});
            }
          }
        } else if (std::holds_alternative<_After_LNode>(_frame)) {
          auto _f = std::move(std::get<_After_LNode>(_frame));
          _stack.emplace_back(_Combine_LNode{std::move(_result), _f.max_val});
          _stack.emplace_back(_Enter{_f.a1, std::move(_f.a10)});
        } else {
          auto _f = std::move(std::get<_Combine_LNode>(_frame));
          _result = ltree::lnode(_f.max_val, std::move(_result),
                                 std::move(_f._result));
        }
      }
      return _result;
    }

    template <typename T1, typename F0, typename F1>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F1 &, uint64_t &, ltree &, T1 &,
                                     ltree &, T1 &>
    T1 ltree_rec(F0 &&f, F1 &&f0) const {
      const ltree *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const ltree *_self;
      };

      /// _After_LNode: saves [a1_0, a2, a1_1, a0], dispatches next recursive
      /// call.
      struct _After_LNode {
        ltree *a1_0;
        ltree a2;
        ltree a1_1;
        uint64_t a0;
      };

      /// _Combine_LNode: receives partial results, combines with _result from
      /// final call.
      struct _Combine_LNode {
        std::decay_t<T1> _result;
        ltree a2;
        ltree a1;
        uint64_t a0;
      };

      using _Frame = std::variant<_Enter, _After_LNode, _Combine_LNode>;
      T1 _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified ltree_rec: _Enter -> _After_LNode -> _Combine_LNode.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const ltree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename ltree::LLeaf>(_sv.v())) {
            const auto &[a0] = std::get<typename ltree::LLeaf>(_sv.v());
            _result = f(a0);
          } else {
            const auto &[a0, a1, a2] = std::get<typename ltree::LNode>(_sv.v());
            _stack.emplace_back(_After_LNode{crane_raw(a1), *a2, *a1, a0});
            _stack.emplace_back(_Enter{crane_raw(a2)});
          }
        } else if (std::holds_alternative<_After_LNode>(_frame)) {
          auto _f = std::move(std::get<_After_LNode>(_frame));
          _stack.emplace_back(_Combine_LNode{
              std::move(_result), std::move(_f.a2), std::move(_f.a1_1), _f.a0});
          _stack.emplace_back(_Enter{_f.a1_0});
        } else {
          auto _f = std::move(std::get<_Combine_LNode>(_frame));
          _result = f0(_f.a0, std::move(_f.a1), std::move(_result),
                       std::move(_f.a2), std::move(_f._result));
        }
      }
      return _result;
    }

    template <typename T1, typename F0, typename F1>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F1 &, uint64_t &, ltree &, T1 &,
                                     ltree &, T1 &>
    T1 ltree_rect(F0 &&f, F1 &&f0) const {
      const ltree *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const ltree *_self;
      };

      /// _After_LNode: saves [a1_0, a2, a1_1, a0], dispatches next recursive
      /// call.
      struct _After_LNode {
        ltree *a1_0;
        ltree a2;
        ltree a1_1;
        uint64_t a0;
      };

      /// _Combine_LNode: receives partial results, combines with _result from
      /// final call.
      struct _Combine_LNode {
        std::decay_t<T1> _result;
        ltree a2;
        ltree a1;
        uint64_t a0;
      };

      using _Frame = std::variant<_Enter, _After_LNode, _Combine_LNode>;
      T1 _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified ltree_rect: _Enter -> _After_LNode -> _Combine_LNode.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const ltree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename ltree::LLeaf>(_sv.v())) {
            const auto &[a0] = std::get<typename ltree::LLeaf>(_sv.v());
            _result = f(a0);
          } else {
            const auto &[a0, a1, a2] = std::get<typename ltree::LNode>(_sv.v());
            _stack.emplace_back(_After_LNode{crane_raw(a1), *a2, *a1, a0});
            _stack.emplace_back(_Enter{crane_raw(a2)});
          }
        } else if (std::holds_alternative<_After_LNode>(_frame)) {
          auto _f = std::move(std::get<_After_LNode>(_frame));
          _stack.emplace_back(_Combine_LNode{
              std::move(_result), std::move(_f.a2), std::move(_f.a1_1), _f.a0});
          _stack.emplace_back(_Enter{_f.a1_0});
        } else {
          auto _f = std::move(std::get<_Combine_LNode>(_frame));
          _result = f0(_f.a0, std::move(_f.a1), std::move(_result),
                       std::move(_f.a2), std::move(_f._result));
        }
      }
      return _result;
    }
  };
};

#endif // INCLUDED_LOOPIFY_STRUCTURES
