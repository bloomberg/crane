#ifndef INCLUDED_PAIR_SELF_DEEP_COPY
#define INCLUDED_PAIR_SELF_DEEP_COPY

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

struct PairSelfDeepCopy {
  /// Like the option case, but the recursive occurrence is hidden under
  /// prod.  The generated C++ currently represents the field as an owned
  /// std::pair containing an owned recursive value.  Clone generation then
  /// emits invalid C++ that calls .clone() on the std::pair object itself, so
  /// this test fails at C++ compile time.
  struct chain {
    // TYPES
    struct Stop {};

    struct Link {
      std::shared_ptr<std::pair<std::shared_ptr<chain>, bool>> a0;
    };

    using variant_t = std::variant<Stop, Link>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    chain() {}

    explicit chain(Stop _v) : v_(_v) {}

    explicit chain(Link _v) : v_(std::move(_v)) {}

    chain(const chain &_other) : v_(std::move(_other.clone().v_)) {}

    chain(chain &&_other) noexcept : v_(std::move(_other.v_)) {}

    chain &operator=(const chain &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    chain &operator=(chain &&_other) noexcept {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    chain clone() const {
      chain _out{};

      struct _CloneFrame {
        const chain *_src;
        chain *_dst;
      };

      std::vector<_CloneFrame> _stack{};
      _stack.reserve(8);
      _stack.push_back({this, &_out});
      while (!_stack.empty()) {
        auto _frame = _stack.back();
        _stack.pop_back();
        const chain *_src = _frame._src;
        chain *_dst = _frame._dst;
        if (std::holds_alternative<Stop>(_src->v())) {
          _dst->v_ = Stop{};
        } else {
          const auto &_alt = std::get<Link>(_src->v());
          _dst->v_ = Link{
              _alt.a0
                  ? std::make_shared<std::pair<std::shared_ptr<chain>, bool>>(
                        std::make_pair(_alt.a0->first
                                           ? std::make_shared<chain>()
                                           : nullptr,
                                       _alt.a0->second))
                  : nullptr};
          auto &_dst_alt = std::get<Link>(_dst->v_);
          if (_alt.a0 && _alt.a0->first) {
            _stack.push_back({_alt.a0->first.get(), _dst_alt.a0->first.get()});
          }
        }
      }
      return _out;
    }

    // CREATORS
    static chain stop() { return chain(Stop{}); }

    static chain link(std::pair<std::shared_ptr<chain>, bool> a0) {
      return chain(
          Link{std::make_shared<std::pair<std::shared_ptr<chain>, bool>>(
              std::move(a0))});
    }

    // MANIPULATORS
    ~chain() {
      std::vector<std::shared_ptr<chain>> _stack{};
      _stack.reserve(8);
      auto _drain = [&](chain &_node) {
        if (std::holds_alternative<Link>(_node.v_)) {
          auto &_alt = std::get<Link>(_node.v_);
          if (_alt.a0 && _alt.a0->first) {
            _stack.push_back(std::move(_alt.a0->first));
          }
        }
      };
      _drain(*this);
      while (!_stack.empty()) {
        auto _node = std::move(_stack.back());
        _stack.pop_back();
        if (_node) {
          _drain(*_node);
        }
      }
    }

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F1>
    requires std::is_invocable_r_v<T1, F1 &, std::pair<chain, bool> &>
  static T1 chain_rect(T1 f, F1 &&f0, const chain &c) {
    if (std::holds_alternative<typename chain::Stop>(c.v())) {
      return f;
    } else {
      const auto &[a0] = std::get<typename chain::Link>(c.v());
      return f0(*a0);
    }
  }

  template <typename T1, typename F1>
    requires std::is_invocable_r_v<T1, F1 &, std::pair<chain, bool> &>
  static T1 chain_rec(T1 f, F1 &&f0, const chain &c) {
    if (std::holds_alternative<typename chain::Stop>(c.v())) {
      return f;
    } else {
      const auto &[a0] = std::get<typename chain::Link>(c.v());
      return f0(*a0);
    }
  }

  static std::pair<chain, chain> dup_chain(chain c);
};

#endif // INCLUDED_PAIR_SELF_DEEP_COPY
