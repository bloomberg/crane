#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
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

struct FetchWindowNextPtr {
  static std::shared_ptr<List<unsigned int>>
  drop(const unsigned int n, std::shared_ptr<List<unsigned int>> l);

  static std::optional<std::pair<unsigned int, unsigned int>>
  fetch_window(const std::shared_ptr<List<unsigned int>> &rom,
               const unsigned int addr);

  static inline const unsigned int t = [](void) {
    if (fetch_window(
            List<unsigned int>::ctor::cons_(
                (((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1),
                List<unsigned int>::ctor::cons_(
                    ((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1),
                    List<unsigned int>::ctor::cons_(
                        (((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1),
                        List<unsigned int>::ctor::nil_()))),
            0)
            .has_value()) {
      std::pair<unsigned int, unsigned int> p = *fetch_window(
          List<unsigned int>::ctor::cons_(
              (((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1),
              List<unsigned int>::ctor::cons_(
                  ((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1),
                  List<unsigned int>::ctor::cons_(
                      (((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1),
                      List<unsigned int>::ctor::nil_()))),
          0);
      unsigned int _x = p.first;
      unsigned int next = p.second;
      return std::move(next);
    } else {
      return 0;
    }
  }();
};
