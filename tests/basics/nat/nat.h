#include <any>
#include <functional>
#include <iostream>
#include <memory>
#include <string>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

struct Nat {
  struct nat {
  public:
    struct O {};
    struct S {
      std::shared_ptr<nat> _a0;
    };
    using variant_t = std::variant<O, S>;

  private:
    variant_t v_;
    explicit nat(O _v) : v_(std::move(_v)) {}
    explicit nat(S _v) : v_(std::move(_v)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<nat> O_() {
        return std::shared_ptr<nat>(new nat(O{}));
      }
      static std::shared_ptr<nat> S_(const std::shared_ptr<nat> &a0) {
        return std::shared_ptr<nat>(new nat(S{a0}));
      }
    };
    const variant_t &v() const { return v_; }
    template <typename T1, MapsTo<T1, std::shared_ptr<nat>, T1> F1>
    T1 nat_rect(const T1 f, F1 &&f0) const {
      return std::visit(
          Overloaded{[&](const typename nat::O _args) -> T1 { return f; },
                     [&](const typename nat::S _args) -> T1 {
                       std::shared_ptr<nat> n0 = _args._a0;
                       return f0(n0, n0->nat_rect(f, f0));
                     }},
          this->v());
    }
    template <typename T1, MapsTo<T1, std::shared_ptr<nat>, T1> F1>
    T1 nat_rec(const T1 f, F1 &&f0) const {
      return std::visit(
          Overloaded{[&](const typename nat::O _args) -> T1 { return f; },
                     [&](const typename nat::S _args) -> T1 {
                       std::shared_ptr<nat> n0 = _args._a0;
                       return f0(n0, n0->nat_rec(f, f0));
                     }},
          this->v());
    }
    std::shared_ptr<nat> add(const std::shared_ptr<nat> &n) const {
      return std::visit(
          Overloaded{[&](const typename nat::O _args) -> std::shared_ptr<nat> {
                       return n;
                     },
                     [&](const typename nat::S _args) -> std::shared_ptr<nat> {
                       std::shared_ptr<nat> x = _args._a0;
                       return nat::ctor::S_(x->add(n));
                     }},
          this->v());
    }
    int nat_to_int() const {
      return std::visit(
          Overloaded{[](const typename nat::O _args) -> int { return 0; },
                     [](const typename nat::S _args) -> int {
                       std::shared_ptr<nat> n_ = _args._a0;
                       return 1 + n_->nat_to_int();
                     }},
          this->v());
    }
  };
};
