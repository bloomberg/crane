#ifndef INCLUDED_CROSS_UNIT_DUPLICATE_SYMBOL_LIB
#define INCLUDED_CROSS_UNIT_DUPLICATE_SYMBOL_LIB

#include <atomic>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

struct Lib {
  struct lst {
    // TYPES
    struct Nil {};

    struct Cons {
      uint64_t a0;
      std::shared_ptr<lst> a1;
    };

    using variant_t = std::variant<Nil, Cons>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    lst() {}

    explicit lst(Nil _v) : v_(_v) {}

    explicit lst(Cons _v) : v_(std::move(_v)) {}

    static lst nil() { return lst(Nil{}); }

    static lst cons(uint64_t a0, lst a1) {
      return lst(Cons{a0, std::make_shared<lst>(std::move(a1))});
    }

    // MANIPULATORS
    ~lst() {
      auto _next = [&](variant_t &_v) -> std::shared_ptr<lst> {
        if (auto *_alt = std::get_if<Cons>(&_v)) {
          if (_alt->a1 && _alt->a1.use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            return std::move(_alt->a1);
          }
        }
        return nullptr;
      };
      std::shared_ptr<lst> _cur = _next(v_mut());
      while (_cur) {
        _cur = _next(_cur->v_mut());
      }
    }

    lst(const lst &) = default;
    lst &operator=(const lst &) = default;
    lst(lst &&) noexcept = default;
    lst &operator=(lst &&) noexcept = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F1>
    requires std::is_invocable_r_v<T1, F1 &, uint64_t &, lst &, T1 &>
  static T1 lst_rect(T1 f, F1 &&f0, const lst &l) {
    if (std::holds_alternative<typename lst::Nil>(l.v())) {
      return f;
    } else {
      const auto &[a0, a1] = std::get<typename lst::Cons>(l.v());
      return f0(a0, *a1, lst_rect<T1>(std::move(f), f0, *a1));
    }
  }

  template <typename T1, typename F1>
    requires std::is_invocable_r_v<T1, F1 &, uint64_t &, lst &, T1 &>
  static T1 lst_rec(T1 f, F1 &&f0, const lst &l) {
    if (std::holds_alternative<typename lst::Nil>(l.v())) {
      return f;
    } else {
      const auto &[a0, a1] = std::get<typename lst::Cons>(l.v());
      return f0(a0, *a1, lst_rec<T1>(std::move(f), f0, *a1));
    }
  }

  static uint64_t len(const lst &l);
};

#endif // INCLUDED_CROSS_UNIT_DUPLICATE_SYMBOL_LIB
