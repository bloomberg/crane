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
      std::shared_ptr<Nat::nat> _a0;
    };
    using variant_t = std::variant<O, S>;

  private:
    variant_t v_;
    explicit nat(O _v) : v_(std::move(_v)) {}
    explicit nat(S _v) : v_(std::move(_v)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<Nat::nat> O_() {
        return std::shared_ptr<Nat::nat>(new Nat::nat(O{}));
      }
      static std::shared_ptr<Nat::nat> S_(const std::shared_ptr<Nat::nat> &a0) {
        return std::shared_ptr<Nat::nat>(new Nat::nat(S{a0}));
      }
    };
    const variant_t &v() const { return v_; }
  };
};

struct RApply {
  struct R {
    std::function<std::shared_ptr<Nat::nat>(std::shared_ptr<Nat::nat>,
                                            std::shared_ptr<Nat::nat>)>
        f;
    std::shared_ptr<Nat::nat> _tag;
  };

  static std::shared_ptr<Nat::nat> f(const std::shared_ptr<R> &,
                                     const std::shared_ptr<Nat::nat> &,
                                     const std::shared_ptr<Nat::nat> &);

  static std::shared_ptr<Nat::nat> _tag(const std::shared_ptr<R> &r);

  static std::shared_ptr<Nat::nat>
  apply_record(const std::shared_ptr<R> &r, const std::shared_ptr<Nat::nat> &a,
               const std::shared_ptr<Nat::nat> &b);
};
