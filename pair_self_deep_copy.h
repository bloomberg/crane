#ifndef INCLUDED_PAIR_SELF_DEEP_COPY
#define INCLUDED_PAIR_SELF_DEEP_COPY

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept CraneMapsTo_ = std::is_invocable_v<F &, Args &...>;

struct PairSelfDeepCopy {
  struct chain {
    // TYPES
    struct Stop {};

    struct Link {
      std::unique_ptr<std::pair<std::unique_ptr<chain>, bool>> d_a0;
    };

    using variant_t = std::variant<Stop, Link>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    chain() {}

    explicit chain(Stop _v) : d_v_(_v) {}

    explicit chain(Link _v) : d_v_(std::move(_v)) {}

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
        const auto &[d_a0] = std::get<Link>(_sv.v());
        return chain(
            Link{d_a0 ? std::make_unique<std::pair<
                            std::unique_ptr<PairSelfDeepCopy::chain>, bool>>(
                            std::make_pair(
                                d_a0->first
                                    ? std::make_unique<PairSelfDeepCopy::chain>(
                                          d_a0->first->clone())
                                    : nullptr,
                                d_a0->second))
                      : nullptr});
      }
    }

    // CREATORS
    static chain stop() { return chain(Stop{}); }

    static chain link(std::pair<std::unique_ptr<chain>, bool> a0) {
      return chain(
          Link{std::make_unique<std::pair<std::unique_ptr<chain>, bool>>(
              std::move(a0))});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    const variant_t &v() const { return d_v_; }
  };

  template <typename T1, CraneMapsTo_<T1, std::pair<chain, bool>> F1>
  static T1 chain_rect(const T1 f, F1 &&f0, const chain &c) {
    if (std::holds_alternative<typename chain::Stop>(c.v())) {
      return f;
    } else {
      const auto &[d_a0] = std::get<typename chain::Link>(c.v());
      return f0(*(d_a0));
    }
  }

  template <typename T1, CraneMapsTo_<T1, std::pair<chain, bool>> F1>
  static T1 chain_rec(const T1 f, F1 &&f0, const chain &c) {
    if (std::holds_alternative<typename chain::Stop>(c.v())) {
      return f;
    } else {
      const auto &[d_a0] = std::get<typename chain::Link>(c.v());
      return f0(*(d_a0));
    }
  }

  static std::pair<chain, chain> dup_chain(chain c);
};

#endif // INCLUDED_PAIR_SELF_DEEP_COPY
