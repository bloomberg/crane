#ifndef INCLUDED_PAIR_SELF_DEEP_COPY
#define INCLUDED_PAIR_SELF_DEEP_COPY

#include <memory>
#include <optional>
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
          _dst->d_v_ = Stop{};
        } else {
          const auto &_alt = std::get<Link>(_src->v());
          _dst->d_v_ = Link{
              _alt.d_a0
                  ? std::make_unique<std::pair<std::unique_ptr<chain>, bool>>(
                        std::make_pair(_alt.d_a0->first
                                           ? std::make_unique<chain>()
                                           : nullptr,
                                       _alt.d_a0->second))
                  : nullptr};
          auto &_dst_alt = std::get<Link>(_dst->d_v_);
          if (_alt.d_a0 && _alt.d_a0->first) {
            _stack.push_back(
                {_alt.d_a0->first.get(), _dst_alt.d_a0->first.get()});
          }
        }
      }
      return _out;
    }

    // CREATORS
    static chain stop() { return chain(Stop{}); }

    static chain link(std::pair<std::unique_ptr<chain>, bool> a0) {
      return chain(
          Link{std::make_unique<std::pair<std::unique_ptr<chain>, bool>>(
              std::move(a0))});
    }

    // MANIPULATORS
    ~chain() {
      std::vector<std::unique_ptr<chain>> _stack{};
      _stack.reserve(8);
      auto _drain = [&](chain &_node) {
        if (std::holds_alternative<Link>(_node.d_v_)) {
          auto &_alt = std::get<Link>(_node.d_v_);
          if (_alt.d_a0 && _alt.d_a0->first) {
            _stack.push_back(std::move(_alt.d_a0->first));
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

    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    const variant_t &v() const { return d_v_; }
  };

  template <typename T1, typename F1>
    requires std::is_invocable_r_v<T1, F1 &, std::pair<chain, bool> &>
  static T1 chain_rect(T1 f, F1 &&f0, const chain &c) {
    if (std::holds_alternative<typename chain::Stop>(c.v())) {
      return f;
    } else {
      const auto &[d_a0] = std::get<typename chain::Link>(c.v());
      return f0(*(d_a0));
    }
  }

  template <typename T1, typename F1>
    requires std::is_invocable_r_v<T1, F1 &, std::pair<chain, bool> &>
  static T1 chain_rec(T1 f, F1 &&f0, const chain &c) {
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
