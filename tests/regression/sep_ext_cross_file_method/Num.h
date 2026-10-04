#ifndef INCLUDED_NUM
#define INCLUDED_NUM

#include <atomic>
#include <memory>
#include <utility>
#include <variant>

namespace Num {

struct Num;

struct Num {
  // TYPES
  struct Zero {};

  struct Succ {
    std::shared_ptr<Num> n;
  };

  using variant_t = std::variant<Zero, Succ>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Num() {}

  explicit Num(Zero _v) : v_(_v) {}

  explicit Num(Succ _v) : v_(std::move(_v)) {}

  static Num zero() { return Num(Zero{}); }

  static Num succ(Num n) {
    return Num(Succ{std::make_shared<Num>(std::move(n))});
  }

  // MANIPULATORS
  ~Num() {
    auto _next = [&](variant_t &_v) -> std::shared_ptr<Num> {
      if (auto *_alt = std::get_if<Succ>(&_v)) {
        if (_alt->n && _alt->n.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          return std::move(_alt->n);
        }
      }
      return nullptr;
    };
    std::shared_ptr<Num> _cur = _next(v_mut());
    while (_cur) {
      _cur = _next(_cur->v_mut());
    }
  }

  Num(const Num &) = default;
  Num &operator=(const Num &) = default;
  Num(Num &&) noexcept = default;
  Num &operator=(Num &&) noexcept = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

} // namespace Num

#endif // INCLUDED_NUM
