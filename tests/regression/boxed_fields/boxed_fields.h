#ifndef INCLUDED_BOXED_FIELDS
#define INCLUDED_BOXED_FIELDS

#include "crane_fn.h"
#include "field.h"
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
    crane::field<A> a;
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
      : v_(crane_convert_spine(
            _other, std::shared_ptr<List<A>>(nullptr),
            [](const List<CraneU> &_cell) -> const List<CraneU> * {
              if (std::holds_alternative<typename List<CraneU>::Cons>(
                      _cell.v())) {
                return std::get<typename List<CraneU>::Cons>(_cell.v()).l.get();
              } else {
                return nullptr;
              }
            },
            [&](const List<CraneU> &_other,
                std::shared_ptr<List<A>> _below) -> variant_t {
              if (std::holds_alternative<typename List<CraneU>::Nil>(
                      _other.v())) {
                return Nil{};
              } else {
                const auto &[a, l] =
                    std::get<typename List<CraneU>::Cons>(_other.v());
                return Cons{
                    [&]() -> A {
                      if constexpr (crane_convertible<A, const CraneU &>) {
                        return crane_convert<A>(crane::unbox(a));
                      } else {
                        throw std::logic_error(
                            "unreachable: inactive constructor field at this "
                            "instantiation");
                      }
                    }(),
                    std::move(_below)};
              }
            },
            [](auto &&_alt) {
              return std::make_shared<List<A>>(std::move(_alt));
            })) {}

  static List<A> nil() { return List<A>(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List<A>(Cons{crane::field<A>(std::move(a)),
                        std::make_shared<List<A>>(std::move(l))});
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

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, T1 &&, A>
  T1 fold_left(F0 &&f, T1 a0) const {
    const List<A> *_loop_self = this;
    T1 _loop_a0 = std::move(a0);
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
        return _loop_a0;
      } else {
        const auto &[a1, a2] = std::get<typename List<A>::Cons>(_sv.v());
        _loop_self = crane_raw(a2);
        _loop_a0 = f(std::move(_loop_a0), crane::unbox(a1));
      }
    }
  }
};

struct BoxedFields {
  struct point {
    // DATA
    uint64_t a0;
    uint64_t a1;

    // ACCESSORS
    point clone() const { return {a0, a1}; }

    // CREATORS
    static point pt(uint64_t a0, uint64_t a1) { return {a0, a1}; }

    uint64_t py() const {
      const auto &[a0, a1] = *this;
      return a1;
    }

    uint64_t px() const {
      const auto &[a0, a1] = *this;
      return a0;
    }

    template <typename T1, typename F0> T1 point_rec(F0 &&f) const {
      return this->template point_rect<T1>(f);
    }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, const uint64_t &,
                                     const uint64_t &>
    T1 point_rect(F0 &&f) const {
      const auto &[a0, a1] = *this;
      return f(a0, a1);
    }
  };

  struct shape {
    // TYPES
    struct Circle {
      std::shared_ptr<point> a0;
      uint64_t a1;
    };

    struct Poly {
      std::shared_ptr<List<point>> a0;
    };

    /// Fields typed by a parameter: boxed or not per instantiation.
    struct Tagged {
      std::shared_ptr<std::optional<point>> a0;
      std::shared_ptr<std::pair<uint64_t, point>> a1;
    };

    using variant_t = std::variant<Circle, Poly, Tagged>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    shape() {}

    explicit shape(Circle _v) : v_(std::move(_v)) {}

    explicit shape(Poly _v) : v_(std::move(_v)) {}

    explicit shape(Tagged _v) : v_(std::move(_v)) {}

    static shape circle(point a0, uint64_t a1) {
      return shape(Circle{std::make_shared<point>(std::move(a0)), a1});
    }

    static shape poly(List<point> a0) {
      return shape(Poly{std::make_shared<List<point>>(std::move(a0))});
    }

    /// Fields typed by a parameter: boxed or not per instantiation.
    static shape tagged(std::optional<point> a0,
                        std::pair<uint64_t, point> a1) {
      return shape(
          Tagged{std::make_shared<std::optional<point>>(std::move(a0)),
                 std::make_shared<std::pair<uint64_t, point>>(std::move(a1))});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    uint64_t weight() const {
      if (std::holds_alternative<typename shape::Circle>(this->v())) {
        const auto &[a0, a1] = std::get<typename shape::Circle>(this->v());
        return ((a0->px() + a0->py()) + a1);
      } else if (std::holds_alternative<typename shape::Poly>(this->v())) {
        const auto &[a0] = std::get<typename shape::Poly>(this->v());
        const List<point> &a0_value = *a0;
        return a0_value.template fold_left<uint64_t>(
            [](uint64_t acc, const point &p) {
              return ((acc + p.px()) + p.py());
            },
            UINT64_C(0));
      } else {
        const auto &[a0, a1] = std::get<typename shape::Tagged>(this->v());
        const auto &[n, p] = (*a1);
        return ((n + p.px()) + [&]() -> uint64_t {
          if ((*a0).has_value()) {
            const point &q = *(*a0);
            return q.py();
          } else {
            return UINT64_C(0);
          }
        }());
      }
    }
  };

  template <typename T1, typename F0, typename F1, typename F2>
  static T1 shape_rect(F0 &&f, F1 &&f0, F2 &&f1, const shape &s) {
    if (std::holds_alternative<typename shape::Circle>(s.v())) {
      const auto &[a0, a1] = std::get<typename shape::Circle>(s.v());
      return f(*a0, a1);
    } else if (std::holds_alternative<typename shape::Poly>(s.v())) {
      const auto &[a0] = std::get<typename shape::Poly>(s.v());
      return f0(*a0);
    } else {
      const auto &[a0, a1] = std::get<typename shape::Tagged>(s.v());
      return f1(*a0, *a1);
    }
  }

  template <typename T1, typename F0, typename F1, typename F2>
  static T1 shape_rec(F0 &&f, F1 &&f0, F2 &&f1, const shape &s) {
    return shape_rect<T1>(f, f0, f1, s);
  }

  static List<point> shift(uint64_t d, const List<point> &ps);

  struct scene {
    // TYPES
    struct Empty {};

    struct Layer {
      std::shared_ptr<shape> a0;
      std::shared_ptr<scene> a1;
    };

    using variant_t = std::variant<Empty, Layer>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    scene() {}

    explicit scene(Empty _v) : v_(_v) {}

    explicit scene(Layer _v) : v_(std::move(_v)) {}

    static scene empty() { return scene(Empty{}); }

    static scene layer(shape a0, scene a1) {
      return scene(Layer{std::make_shared<shape>(std::move(a0)),
                         std::make_shared<scene>(std::move(a1))});
    }

    // MANIPULATORS
    ~scene() {
      auto _next = [&](variant_t &_v) -> std::shared_ptr<scene> {
        if (auto *_alt = std::get_if<Layer>(&_v)) {
          if (_alt->a1 && _alt->a1.use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            return std::move(_alt->a1);
          }
        }
        return nullptr;
      };
      std::shared_ptr<scene> _cur = _next(v_mut());
      while (_cur) {
        _cur = _next(_cur->v_mut());
      }
    }

    scene(const scene &) = default;
    scene &operator=(const scene &) = default;
    scene(scene &&) = default;
    scene &operator=(scene &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    scene move_all(uint64_t d) const {
      std::optional<scene> _root{};
      std::shared_ptr<scene> *_write = nullptr;
      const scene *_loop_self = this;
      while (true) {
        auto &&_sv = *_loop_self;
        if (std::holds_alternative<typename scene::Empty>(_sv.v())) {
          auto _value = scene::empty();
          (_write ? *(*_write = std::make_shared<scene>(std::move(_value)))
                  : _root.emplace(std::move(_value)));
          break;
        } else {
          const auto &[a0, a1] = std::get<typename scene::Layer>(_sv.v());
          auto &&_sv0 = *a0;
          if (std::holds_alternative<typename shape::Circle>(_sv0.v())) {
            const auto &[a00, a10] = std::get<typename shape::Circle>(_sv0.v());
            const auto &_sv1 = *a00;
            const auto &[a01, a11] = _sv1;
            auto _cell = typename scene::Layer(
                std::make_shared<std::decay_t<decltype(shape::circle(
                    point::pt((a01 + d), a11), a10))>>(
                    shape::circle(point::pt((a01 + d), a11), a10)),
                nullptr);
            scene &_node =
                (_write ? *(*_write = std::make_shared<scene>(std::move(_cell)))
                        : _root.emplace(std::move(_cell)));
            _write = &std::get<typename scene::Layer>(_node.v_mut()).a1;
            _loop_self = crane_raw(a1);
            continue;
          } else if (std::holds_alternative<typename shape::Poly>(_sv0.v())) {
            const auto &[a00] = std::get<typename shape::Poly>(_sv0.v());
            auto _cell = typename scene::Layer(
                std::make_shared<
                    std::decay_t<decltype(shape::poly(shift(d, *a00)))>>(
                    shape::poly(shift(d, *a00))),
                nullptr);
            scene &_node =
                (_write ? *(*_write = std::make_shared<scene>(std::move(_cell)))
                        : _root.emplace(std::move(_cell)));
            _write = &std::get<typename scene::Layer>(_node.v_mut()).a1;
            _loop_self = crane_raw(a1);
            continue;
          } else {
            auto _cell = typename scene::Layer(
                std::make_shared<std::decay_t<decltype(*a0)>>(*a0), nullptr);
            scene &_node =
                (_write ? *(*_write = std::make_shared<scene>(std::move(_cell)))
                        : _root.emplace(std::move(_cell)));
            _write = &std::get<typename scene::Layer>(_node.v_mut()).a1;
            _loop_self = crane_raw(a1);
            continue;
          }
        }
      }
      return std::move(*_root);
    }

    uint64_t total() const {
      const scene *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const scene *_self;
      };

      /// CraneCont_Layer: saves [a0], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Layer {
        std::shared_ptr<shape> a0;
      };

      using CraneFrame = std::variant<CraneEnter, CraneCont_Layer>;
      uint64_t _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified total: CraneEnter -> CraneCont_Layer.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const scene *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename scene::Empty>(_sv.v())) {
            _result = UINT64_C(0);
          } else {
            const auto &[a0, a1] = std::get<typename scene::Layer>(_sv.v());
            _stack.emplace_back(CraneCont_Layer{a0});
            _stack.emplace_back(CraneEnter{crane_raw(a1)});
          }
        } else {
          auto _f = std::move(std::get<CraneCont_Layer>(_frame));
          std::shared_ptr<shape> a0 = std::move(_f.a0);
          _result = (a0->weight() + std::move(_result));
        }
      }
      return _result;
    }

    template <typename T1, typename F1>
    T1 scene_rec(const T1 &f, F1 &&f0) const {
      return this->template scene_rect<T1>(f, f0);
    }

    template <typename T1, typename F1> T1 scene_rect(T1 f, F1 &&f0) const {
      const scene *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const scene *_self;
      };

      /// CraneCont_Layer: saves [a0, a1], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Layer {
        std::shared_ptr<shape> a0;
        std::shared_ptr<scene> a1;
      };

      using CraneFrame = std::variant<CraneEnter, CraneCont_Layer>;
      T1 _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified scene_rect: CraneEnter -> CraneCont_Layer.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const scene *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename scene::Empty>(_sv.v())) {
            _result = f;
          } else {
            const auto &[a0, a1] = std::get<typename scene::Layer>(_sv.v());
            _stack.emplace_back(CraneCont_Layer{a0, a1});
            _stack.emplace_back(CraneEnter{crane_raw(a1)});
          }
        } else {
          auto _f = std::move(std::get<CraneCont_Layer>(_frame));
          std::shared_ptr<shape> a0 = std::move(_f.a0);
          std::shared_ptr<scene> a1 = std::move(_f.a1);
          _result = f0(*a0, *a1, std::move(_result));
        }
      }
      return _result;
    }
  };

  static inline const scene sample = scene::layer(
      shape::circle(point::pt(UINT64_C(1), UINT64_C(2)), UINT64_C(3)),
      scene::layer(
          shape::poly(List<point>::cons(
              point::pt(UINT64_C(1), UINT64_C(1)),
              List<point>::cons(
                  point::pt(UINT64_C(2), UINT64_C(2)),
                  List<point>::cons(point::pt(UINT64_C(3), UINT64_C(3)),
                                    List<point>::nil())))),
          scene::layer(shape::tagged(
                           std::make_optional<point>(
                               point::pt(UINT64_C(4), UINT64_C(5))),
                           std::make_pair(UINT64_C(6),
                                          point::pt(UINT64_C(7), UINT64_C(8)))),
                       scene::empty())));
  static constexpr uint64_t sample_total = UINT64_C(36);
  static constexpr uint64_t moved_total = UINT64_C(76);

  /// Fields typed by a parameter: boxed or not per instantiation.
  template <typename A> struct tagged {
    // DATA
    uint64_t a0;
    A a1;

    // ACCESSORS
    tagged<A> clone() const { return {a0, a1}; }

    template <typename CraneU>
      requires crane_convertible<CraneU, const A &>
    operator tagged<CraneU>() const {
      return {a0, crane_convert<CraneU>(a1)};
    }

    // CREATORS
    static tagged<A> tag(uint64_t a0, A a1) { return {a0, std::move(a1)}; }

    uint64_t tag_of() const {
      const auto &[a0, a1] = *this;
      return a0;
    }

    A untag() const {
      const auto &[a0, a1] = *this;
      return crane::unbox(a1);
    }

    template <typename T1, typename F0> T1 tagged_rec(F0 &&f) const {
      return this->template tagged_rect<T1>(f);
    }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, const uint64_t &, A>
    T1 tagged_rect(F0 &&f) const {
      const auto &[a0, a1] = *this;
      return f(a0, crane::unbox(a1));
    }
  };

  static inline const tagged<scene> heavy =
      tagged<scene>::tag(UINT64_C(1), sample);
  static inline const tagged<uint64_t> light =
      tagged<uint64_t>::tag(UINT64_C(2), UINT64_C(40));
  static constexpr uint64_t heavy_total = UINT64_C(37);
  static constexpr uint64_t light_total = UINT64_C(42);
};

#endif // INCLUDED_BOXED_FIELDS
