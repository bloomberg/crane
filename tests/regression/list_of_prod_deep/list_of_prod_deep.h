#ifndef INCLUDED_LIST_OF_PROD_DEEP
#define INCLUDED_LIST_OF_PROD_DEEP

#include "crane_fn.h"
#include "obj.h"
#include "small_vector.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <stdexcept>
#include <utility>
#include <variant>

struct ListOfProdDeep {
  template <typename A> struct lst {
    // TYPES
    struct Lnil {};

    struct Lcons {
      A a0;
      std::shared_ptr<lst<A>> a1;
    };

    using variant_t = std::variant<Lnil, Lcons>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    lst() {}

    explicit lst(Lnil _v) : v_(_v) {}

    explicit lst(Lcons _v) : v_(std::move(_v)) {}

    template <typename CraneU>
    lst(const lst<CraneU> &_other)
        : v_([&]() -> variant_t {
            if (std::holds_alternative<typename lst<CraneU>::Lnil>(_other.v())) {
              return Lnil{};
            } else {
              const auto &[a0, a1] =
                  std::get<typename lst<CraneU>::Lcons>(_other.v());
              return Lcons{
                  [&]() -> A {
                    if constexpr (crane_convertible<A, const CraneU &>) {
                      return crane_convert<A>(a0);
                    } else {
                      throw std::logic_error("unreachable: inactive "
                                             "constructor field at this "
                                             "instantiation");
                    }
                  }(),
                  (a1 ? std::make_shared<lst<A>>(crane_convert<lst<A>>(*a1))
                      : nullptr)};
            }
          }()) {}

    static lst<A> lnil() { return lst<A>(Lnil{}); }

    static lst<A> lcons(A a0, crane::shared_child_slot<lst<A>> a1) {
      return lst<A>(Lcons{std::move(a0), a1.take()});
    }

    // MANIPULATORS
    ~lst() {
      // Release the children this node alone owns in a loop, not recursively,
      // so a deep value cannot overflow the stack.
      auto _next = [&](variant_t &_v) -> std::shared_ptr<lst<A>> {
        if (auto *_alt = std::get_if<Lcons>(&_v)) {
          if (_alt->a1 && _alt->a1.use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            return std::move(_alt->a1);
          }
        }
        return nullptr;
      };
      std::shared_ptr<lst<A>> _cur = _next(v_mut());
      while (_cur) {
        _cur = _next(_cur->v_mut());
      }
    }

    lst(const lst &) = default;
    lst &operator=(const lst &) = default;
    lst(lst &&) = default;
    lst &operator=(lst &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    template <typename T1, typename F1> T1 lst_rec(T1 f, F1 &&f0) const {
      return this->template lst_rect<T1>(std::move(f), f0);
    }

    template <typename T1, typename F1> T1 lst_rect(T1 f, F1 &&f0) const {
      const lst<A> *_self = this;

      // Explicit stack replaces the non-tail recursion of lst_rect: _call
      // frames are pending calls, _after frames resume a caller.
      struct _call {
        const lst<A> *_self;
      };

      struct _after_lst_rect_in_Lcons {
        A a0;
        std::shared_ptr<lst<A>> a1;
      };

      using _frame = std::variant<_call, _after_lst_rect_in_Lcons>;
      T1 _result{};
      crane::small_vector<_frame> _stack;
      _stack.emplace_back(_call{_self});
      while (!_stack.empty()) {
        _frame &_popped = _stack.back();
        if (std::holds_alternative<_call>(_popped)) {
          auto _f = std::move(std::get<_call>(_popped));
          _stack.pop_back();
          const lst<A> *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename lst<A>::Lnil>(_sv.v())) {
            _result = f;
          } else {
            const auto &[a0, a1] = std::get<typename lst<A>::Lcons>(_sv.v());
            _stack.emplace_back(_after_lst_rect_in_Lcons{a0, a1});
            _stack.emplace_back(_call{crane_raw(a1)});
          }
        } else {
          auto _f = std::move(std::get<_after_lst_rect_in_Lcons>(_popped));
          _stack.pop_back();
          auto a0 = std::move(_f.a0);
          std::shared_ptr<lst<A>> a1 = std::move(_f.a1);
          _result = f0(a0, *a1, std::move(_result));
        }
      }
      return _result;
    }
  };

  struct t {
    // TYPES
    struct Node {
      std::shared_ptr<lst<std::pair<t, uint64_t>>> a0;
    };

    using variant_t = std::variant<Node>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    t() {}

    explicit t(Node _v) : v_(std::move(_v)) {}

    static t node(lst<std::pair<t, uint64_t>> a0) {
      return t(
          Node{std::make_shared<lst<std::pair<t, uint64_t>>>(std::move(a0))});
    }

    // MANIPULATORS
    ~t() {
      // Release the children this node alone owns in a loop, not recursively,
      // so a deep value cannot overflow the stack.
      crane::small_vector<std::shared_ptr<t>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<Node>(&_v)) {
          if (_alt->a0 && _alt->a0.use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            crane::small_vector<std::shared_ptr<lst<std::pair<t,
                                                              uint64_t>>>> _hw1;
            if (auto *_ha5 =
                    std::get_if<typename lst<std::pair<t, uint64_t>>::Lcons>(
                        &(*_alt->a0).v_mut())) {
              _stack.push_back(std::make_shared<t>(std::move(_ha5->a0.first)));
              _hw1.push_back(std::move(_ha5->a1));
            }
            while (!_hw1.empty()) {
              auto _hw1p = std::move(_hw1.back());
              _hw1.pop_back();
              if (!_hw1p || _hw1p.use_count() != 1) {
                continue;
              }
              std::atomic_thread_fence(std::memory_order_acquire);
              auto &_hw1e = *_hw1p;
              if (auto *_ha3 =
                      std::get_if<typename lst<std::pair<t, uint64_t>>::Lcons>(
                          &_hw1e.v_mut())) {
                _stack.push_back(std::make_shared<t>(std::move(_ha3->a0.first)));
                _hw1.push_back(std::move(_ha3->a1));
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

    t(const t &) = default;
    t &operator=(const t &) = default;
    t(t &&) = default;
    t &operator=(t &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    t wrap(uint64_t k) const {
      return t::node(lst<std::pair<t, uint64_t>>::lcons(
          std::make_pair(*this, k), lst<std::pair<t, uint64_t>>::lnil()));
    }

    template <typename T1, typename F0> T1 t_rec(F0 &&f) const {
      return this->template t_rect<T1>(f);
    }

    template <typename T1, typename F0> T1 t_rect(F0 &&f) const {
      const auto &[a0] = std::get<typename t::Node>(this->v());
      return f(*a0);
    }
  };

  static inline const t empty = t::node(lst<std::pair<t, uint64_t>>::lnil());
};

#endif // INCLUDED_LIST_OF_PROD_DEEP
