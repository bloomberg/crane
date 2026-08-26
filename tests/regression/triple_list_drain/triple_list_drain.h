#ifndef INCLUDED_TRIPLE_LIST_DRAIN
#define INCLUDED_TRIPLE_LIST_DRAIN

#include "small_vector.h"
#include <any>
#include <atomic>
#include <memory>
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

  static List<A> nil() { return List(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List(Cons{std::move(a), std::make_shared<List<A>>(std::move(l))});
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
};

struct TripleListDrain {
  struct t {
    // TYPES
    struct Node {
      uint64_t a0;
      std::shared_ptr<List<List<List<t>>>> a1;
    };

    using variant_t = std::variant<Node>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    t() {}

    explicit t(Node _v) : v_(std::move(_v)) {}

    static t node(uint64_t a0, List<List<List<t>>> a1) {
      return t(Node{a0, std::make_shared<List<List<List<t>>>>(std::move(a1))});
    }

    // MANIPULATORS
    ~t() {
      crane::small_vector<std::shared_ptr<t>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<Node>(&_v)) {
          if (_alt->a1 && _alt->a1.use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            crane::small_vector<std::shared_ptr<List<List<List<t>>>>> _hw1;
            if (auto *_ha20 = std::get_if<typename List<List<List<t>>>::Cons>(
                    &((*(_alt->a1))).v_mut())) {
              crane::small_vector<std::shared_ptr<List<List<t>>>> _hw21;
              if (auto *_ha30 = std::get_if<typename List<List<t>>::Cons>(
                      &(_ha20->a).v_mut())) {
                crane::small_vector<std::shared_ptr<List<t>>> _hw31;
                if (auto *_ha35 = std::get_if<typename List<t>::Cons>(
                        &(_ha30->a).v_mut())) {
                  _stack.push_back(std::make_shared<t>(std::move(_ha35->a)));
                  _hw31.push_back(std::move(_ha35->l));
                }
                while (!_hw31.empty()) {
                  auto _hw31p = std::move(_hw31.back());
                  _hw31.pop_back();
                  if (!_hw31p || _hw31p.use_count() != 1) {
                    continue;
                  }
                  std::atomic_thread_fence(std::memory_order_acquire);
                  auto &_hw31e = *_hw31p;
                  if (auto *_ha33 = std::get_if<typename List<t>::Cons>(
                          &(_hw31e).v_mut())) {
                    _stack.push_back(std::make_shared<t>(std::move(_ha33->a)));
                    _hw31.push_back(std::move(_ha33->l));
                  }
                }
                _hw21.push_back(std::move(_ha30->l));
              }
              while (!_hw21.empty()) {
                auto _hw21p = std::move(_hw21.back());
                _hw21.pop_back();
                if (!_hw21p || _hw21p.use_count() != 1) {
                  continue;
                }
                std::atomic_thread_fence(std::memory_order_acquire);
                auto &_hw21e = *_hw21p;
                if (auto *_ha23 = std::get_if<typename List<List<t>>::Cons>(
                        &(_hw21e).v_mut())) {
                  crane::small_vector<std::shared_ptr<List<t>>> _hw24;
                  if (auto *_ha28 = std::get_if<typename List<t>::Cons>(
                          &(_ha23->a).v_mut())) {
                    _stack.push_back(std::make_shared<t>(std::move(_ha28->a)));
                    _hw24.push_back(std::move(_ha28->l));
                  }
                  while (!_hw24.empty()) {
                    auto _hw24p = std::move(_hw24.back());
                    _hw24.pop_back();
                    if (!_hw24p || _hw24p.use_count() != 1) {
                      continue;
                    }
                    std::atomic_thread_fence(std::memory_order_acquire);
                    auto &_hw24e = *_hw24p;
                    if (auto *_ha26 = std::get_if<typename List<t>::Cons>(
                            &(_hw24e).v_mut())) {
                      _stack.push_back(
                          std::make_shared<t>(std::move(_ha26->a)));
                      _hw24.push_back(std::move(_ha26->l));
                    }
                  }
                  _hw21.push_back(std::move(_ha23->l));
                }
              }
              _hw1.push_back(std::move(_ha20->l));
            }
            while (!_hw1.empty()) {
              auto _hw1p = std::move(_hw1.back());
              _hw1.pop_back();
              if (!_hw1p || _hw1p.use_count() != 1) {
                continue;
              }
              std::atomic_thread_fence(std::memory_order_acquire);
              auto &_hw1e = *_hw1p;
              if (auto *_ha3 = std::get_if<typename List<List<List<t>>>::Cons>(
                      &(_hw1e).v_mut())) {
                crane::small_vector<std::shared_ptr<List<List<t>>>> _hw4;
                if (auto *_ha13 = std::get_if<typename List<List<t>>::Cons>(
                        &(_ha3->a).v_mut())) {
                  crane::small_vector<std::shared_ptr<List<t>>> _hw14;
                  if (auto *_ha18 = std::get_if<typename List<t>::Cons>(
                          &(_ha13->a).v_mut())) {
                    _stack.push_back(std::make_shared<t>(std::move(_ha18->a)));
                    _hw14.push_back(std::move(_ha18->l));
                  }
                  while (!_hw14.empty()) {
                    auto _hw14p = std::move(_hw14.back());
                    _hw14.pop_back();
                    if (!_hw14p || _hw14p.use_count() != 1) {
                      continue;
                    }
                    std::atomic_thread_fence(std::memory_order_acquire);
                    auto &_hw14e = *_hw14p;
                    if (auto *_ha16 = std::get_if<typename List<t>::Cons>(
                            &(_hw14e).v_mut())) {
                      _stack.push_back(
                          std::make_shared<t>(std::move(_ha16->a)));
                      _hw14.push_back(std::move(_ha16->l));
                    }
                  }
                  _hw4.push_back(std::move(_ha13->l));
                }
                while (!_hw4.empty()) {
                  auto _hw4p = std::move(_hw4.back());
                  _hw4.pop_back();
                  if (!_hw4p || _hw4p.use_count() != 1) {
                    continue;
                  }
                  std::atomic_thread_fence(std::memory_order_acquire);
                  auto &_hw4e = *_hw4p;
                  if (auto *_ha6 = std::get_if<typename List<List<t>>::Cons>(
                          &(_hw4e).v_mut())) {
                    crane::small_vector<std::shared_ptr<List<t>>> _hw7;
                    if (auto *_ha11 = std::get_if<typename List<t>::Cons>(
                            &(_ha6->a).v_mut())) {
                      _stack.push_back(
                          std::make_shared<t>(std::move(_ha11->a)));
                      _hw7.push_back(std::move(_ha11->l));
                    }
                    while (!_hw7.empty()) {
                      auto _hw7p = std::move(_hw7.back());
                      _hw7.pop_back();
                      if (!_hw7p || _hw7p.use_count() != 1) {
                        continue;
                      }
                      std::atomic_thread_fence(std::memory_order_acquire);
                      auto &_hw7e = *_hw7p;
                      if (auto *_ha9 = std::get_if<typename List<t>::Cons>(
                              &(_hw7e).v_mut())) {
                        _stack.push_back(
                            std::make_shared<t>(std::move(_ha9->a)));
                        _hw7.push_back(std::move(_ha9->l));
                      }
                    }
                    _hw4.push_back(std::move(_ha6->l));
                  }
                }
                _hw1.push_back(std::move(_ha3->l));
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

    t(const t &) = default;
    t &operator=(const t &) = default;
    t(t &&) noexcept = default;
    t &operator=(t &&) noexcept = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, uint64_t &, List<List<List<t>>> &>
  static T1 t_rect(F0 &&f, const t &t0) {
    const auto &[a0, a1] = std::get<typename t::Node>(t0.v());
    return f(a0, *a1);
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, uint64_t &, List<List<List<t>>> &>
  static T1 t_rec(F0 &&f, const t &t0) {
    const auto &[a0, a1] = std::get<typename t::Node>(t0.v());
    return f(a0, *a1);
  }

  static t wrap(uint64_t k, t acc);
  static inline const t empty =
      t::node(UINT64_C(0), List<List<List<t>>>::nil());
};

#endif // INCLUDED_TRIPLE_LIST_DRAIN
