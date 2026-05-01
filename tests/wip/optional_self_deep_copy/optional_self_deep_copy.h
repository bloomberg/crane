#ifndef INCLUDED_OPTIONAL_SELF_DEEP_COPY
#define INCLUDED_OPTIONAL_SELF_DEEP_COPY

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

struct OptionalSelfDeepCopy {
  /// Self-recursion hidden under option is not the direct field shape handled
  /// by the iterative clone/destructor generator.  This probes whether Crane
  /// still generates recursive clone/destruct code for option tree.
  struct chain {
    // TYPES
    struct Stop {};

    struct More {
      std::unique_ptr<std::optional<std::unique_ptr<chain>>> d_a0;
    };

    using variant_t = std::variant<Stop, More>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    chain() {}

    explicit chain(Stop _v) : d_v_(_v) {}

    explicit chain(More _v) : d_v_(std::move(_v)) {}

    chain(const chain &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    chain(chain &&_other) : d_v_(std::move(_other.d_v_)) {}

    chain &operator=(const chain &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    chain &operator=(chain &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    chain clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<Stop>(_sv.v())) {
        return chain(Stop{});
      } else {
        const auto &[d_a0] = std::get<More>(_sv.v());
        return chain(
            More{d_a0 ? std::make_unique<std::optional<
                            std::unique_ptr<OptionalSelfDeepCopy::chain>>>(
                            d_a0->clone())
                      : nullptr});
      }
    }

    // CREATORS
    static chain stop() { return chain(Stop{}); }

    static chain more(std::optional<std::unique_ptr<chain>> a0) {
      return chain(More{std::make_unique<std::optional<std::unique_ptr<chain>>>(
          std::move(a0))});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, std::optional<chain>> F1>
  static T1 chain_rect(const T1 f, F1 &&f0, const chain &c) {
    if (std::holds_alternative<typename chain::Stop>(c.v())) {
      return f;
    } else {
      const auto &[d_a0] = std::get<typename chain::More>(c.v());
      return f0(*(d_a0));
    }
  }

  template <typename T1, MapsTo<T1, std::optional<chain>> F1>
  static T1 chain_rec(const T1 f, F1 &&f0, const chain &c) {
    if (std::holds_alternative<typename chain::Stop>(c.v())) {
      return f;
    } else {
      const auto &[d_a0] = std::get<typename chain::More>(c.v());
      return f0(*(d_a0));
    }
  }

  static std::pair<chain, chain> dup_chain(chain c);
};

#endif // INCLUDED_OPTIONAL_SELF_DEEP_COPY
