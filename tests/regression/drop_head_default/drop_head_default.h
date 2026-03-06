#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

template <typename A> struct List {
public:
  struct nil {};
  struct cons {
    A _a0;
    std::shared_ptr<List<A>> _a1;
  };
  using variant_t = std::variant<nil, cons>;

private:
  variant_t v_;
  explicit List(nil _v) : v_(std::move(_v)) {}
  explicit List(cons _v) : v_(std::move(_v)) {}

public:
  struct ctor {
    ctor() = delete;
    static std::shared_ptr<List<A>> nil_() {
      return std::shared_ptr<List<A>>(new List<A>(nil{}));
    }
    static std::shared_ptr<List<A>> cons_(A a0,
                                          const std::shared_ptr<List<A>> &a1) {
      return std::shared_ptr<List<A>>(new List<A>(cons{a0, a1}));
    }
    static std::unique_ptr<List<A>> nil_uptr() {
      return std::unique_ptr<List<A>>(new List<A>(nil{}));
    }
    static std::unique_ptr<List<A>>
    cons_uptr(A a0, const std::shared_ptr<List<A>> &a1) {
      return std::unique_ptr<List<A>>(new List<A>(cons{a0, a1}));
    }
  };
  const variant_t &v() const { return v_; }
  variant_t &v_mut() { return v_; }
};

struct DropHeadDefault {
  template <typename T1>
  static std::shared_ptr<List<T1>> drop(const unsigned int n,
                                        std::shared_ptr<List<T1>> l) {
    if (n <= 0) {
      return std::move(l);
    } else {
      unsigned int n_ = n - 1;
      return std::visit(Overloaded{[](const typename List<T1>::nil _args)
                                       -> std::shared_ptr<List<T1>> {
                                     return List<T1>::ctor::nil_();
                                   },
                                   [&](const typename List<T1>::cons _args)
                                       -> std::shared_ptr<List<T1>> {
                                     std::shared_ptr<List<T1>> l_ = _args._a1;
                                     return drop<T1>(std::move(n_),
                                                     std::move(l_));
                                   }},
                        l->v());
    }
  }

  static unsigned int
  head_after_drop(const std::shared_ptr<List<unsigned int>> &rom,
                  const unsigned int addr);

  static inline const unsigned int t = head_after_drop(
      List<unsigned int>::ctor::cons_(
          (((((0 + 1) + 1) + 1) + 1) + 1),
          List<unsigned int>::ctor::cons_(
              (((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1),
              List<unsigned int>::ctor::cons_(
                  (((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1),
                  List<unsigned int>::ctor::nil_()))),
      (0 + 1));
};
