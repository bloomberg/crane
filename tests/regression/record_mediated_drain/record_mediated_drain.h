#ifndef INCLUDED_RECORD_MEDIATED_DRAIN
#define INCLUDED_RECORD_MEDIATED_DRAIN

#include "small_vector.h"
#include <atomic>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

struct RecordMediatedDrain {
  template <typename A> struct cell {
    uint64_t hd;
    A tl;
  };

  struct t {
    // TYPES
    struct Stop {};

    struct More {
      std::shared_ptr<cell<t>> a0;
    };

    using variant_t = std::variant<Stop, More>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    t() {}

    explicit t(Stop _v) : v_(_v) {}

    explicit t(More _v) : v_(std::move(_v)) {}

    static t stop() { return t(Stop{}); }

    static t more(cell<t> a0) {
      return t(More{std::make_shared<cell<t>>(std::move(a0))});
    }

    // MANIPULATORS
    ~t() {
      crane::small_vector<std::shared_ptr<t>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<More>(&_v)) {
          if (_alt->a0 && _alt->a0.use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            _stack.push_back(
                std::make_shared<t>(std::move(((*(_alt->a0))).tl)));
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

    t(const t &) = default;
    t &operator=(const t &) = default;
    t(t &&) noexcept = default;
    t &operator=(t &&) noexcept = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F1>
    requires std::is_invocable_r_v<T1, F1 &, cell<t> &>
  static T1 t_rect(T1 f, F1 &&f0, const t &t0) {
    if (std::holds_alternative<typename t::Stop>(t0.v())) {
      return f;
    } else {
      const auto &[a0] = std::get<typename t::More>(t0.v());
      return f0(*a0);
    }
  }

  template <typename T1, typename F1>
    requires std::is_invocable_r_v<T1, F1 &, cell<t> &>
  static T1 t_rec(T1 f, F1 &&f0, const t &t0) {
    if (std::holds_alternative<typename t::Stop>(t0.v())) {
      return f;
    } else {
      const auto &[a0] = std::get<typename t::More>(t0.v());
      return f0(*a0);
    }
  }

  static t wrap(uint64_t k, t acc);
  static inline const t empty = t::stop();
};

#endif // INCLUDED_RECORD_MEDIATED_DRAIN
