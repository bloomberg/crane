#ifndef INCLUDED_SEPEXTLISTCLONEQUAL
#define INCLUDED_SEPEXTLISTCLONEQUAL

#include "crane_fn.h"
#include "small_vector.h"
#include <any>
#include <atomic>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

#include "Datatypes.h"

namespace SepExtListCloneQual {

template <typename A> struct Forest;

template <typename A> struct Forest {
  // TYPES
  struct Leaf {};

  struct Node {
    A a0;
    std::shared_ptr<typename Datatypes::template List<Forest<A>>> a1;
  };

  using variant_t = std::variant<Leaf, Node>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Forest() {}

  explicit Forest(Leaf _v) : v_(_v) {}

  explicit Forest(Node _v) : v_(std::move(_v)) {}

  template <typename _U> Forest(const Forest<_U> &_other) {
    if (std::holds_alternative<typename Forest<_U>::Leaf>(_other.v())) {
      this->v_ = Leaf{};
    } else {
      const auto &[a0, a1] = std::get<typename Forest<_U>::Node>(_other.v());
      this->v_ = Node{
          [&]() -> A {
            if constexpr (std::is_same_v<_U, std::any>) {
              return crane_any_cast<A>(a0);
            } else {
              return A(a0);
            }
          }(),
          (a1 ? std::make_shared<typename Datatypes::template List<Forest<A>>>(
                    *a1)
              : nullptr)};
    }
  }

  static Forest<A> leaf() { return Forest<A>(Leaf{}); }

  static Forest<A> node(A a0, typename Datatypes::template List<Forest<A>> a1) {
    return Forest<A>(
        Node{std::move(a0),
             std::make_shared<typename Datatypes::template List<Forest<A>>>(
                 std::move(a1))});
  }

  // MANIPULATORS
  ~Forest() {
    crane::small_vector<std::shared_ptr<Forest<A>>> _stack = {};
    auto _drain = [&](variant_t &_v) {
      if (auto *_alt = std::get_if<Node>(&_v)) {
        if (_alt->a1 && _alt->a1.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          auto _lp = _alt->a1.get();
          while (
              std::holds_alternative<typename Datatypes::List<Forest<A>>::Cons>(
                  _lp->v())) {
            auto &_lc = std::get<typename Datatypes::List<Forest<A>>::Cons>(
                _lp->v_mut());
            _stack.push_back(std::make_shared<Forest<A>>(std::move(_lc.a)));
            if (_lc.l && _lc.l.use_count() == 1) {
              std::atomic_thread_fence(std::memory_order_acquire);
              _lp = _lc.l.get();
            } else {
              break;
            }
          }
          _alt->a1.reset();
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

  Forest(const Forest &) = default;
  Forest &operator=(const Forest &) = default;
  Forest(Forest &&) noexcept = default;
  Forest &operator=(Forest &&) noexcept = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

} // namespace SepExtListCloneQual

#endif // INCLUDED_SEPEXTLISTCLONEQUAL
