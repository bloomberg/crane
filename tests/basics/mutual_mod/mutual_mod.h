#ifndef INCLUDED_MUTUAL_MOD
#define INCLUDED_MUTUAL_MOD

#include <memory>
#include <utility>
#include <variant>
#include <vector>

struct EvenOdd {
  struct even_list;
  struct odd_list;

  struct even_list {
    // TYPES
    struct ENil {};

    struct ECons {
      unsigned int a0;
      std::unique_ptr<odd_list> a1;
    };

    using variant_t = std::variant<ENil, ECons>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    even_list() {}

    explicit even_list(ENil _v) : v_(_v) {}

    explicit even_list(ECons _v) : v_(std::move(_v)) {}

    even_list(const even_list &_other) : v_(std::move(_other.clone().v_)) {}

    even_list(even_list &&_other) : v_(std::move(_other.v_)) {}

    even_list &operator=(const even_list &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    even_list &operator=(even_list &&_other) {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    even_list clone() const {
      even_list _out{};

      struct _CloneFrame {
        const even_list *_src;
        even_list *_dst;
      };

      std::vector<_CloneFrame> _stack{};
      _stack.reserve(8);
      _stack.push_back({this, &_out});
      while (!_stack.empty()) {
        auto _frame = _stack.back();
        _stack.pop_back();
        const even_list *_src = _frame._src;
        even_list *_dst = _frame._dst;
        if (std::holds_alternative<ENil>(_src->v())) {
          _dst->v_ = ENil{};
        } else {
          const auto &_alt = std::get<ECons>(_src->v());
          _dst->v_ =
              ECons{_alt.a0, _alt.a1 ? std::make_unique<odd_list>() : nullptr};
          auto &_dst_alt = std::get<ECons>(_dst->v_);
          if (_alt.a1) {
            if (std::holds_alternative<typename EvenOdd::odd_list::OCons>(
                    _alt.a1->v())) {
              const auto &_psrc =
                  std::get<typename EvenOdd::odd_list::OCons>(_alt.a1->v());
              auto &_pdst = std::get<typename EvenOdd::odd_list::OCons>(
                  _dst_alt.a1->v_mut());
              if (_psrc.a1) {
                _pdst.a1 = std::make_unique<even_list>();
                _stack.push_back({_psrc.a1.get(), _pdst.a1.get()});
              }
            }
          }
        }
      }
      return _out;
    }

    // CREATORS
    static even_list enil() { return even_list(ENil{}); }

    static even_list econs(unsigned int a0, odd_list a1) {
      return even_list(ECons{a0, std::make_unique<odd_list>(std::move(a1))});
    }

    // MANIPULATORS
    ~even_list() {
      std::vector<std::unique_ptr<even_list>> _stack{};
      _stack.reserve(8);
      auto _drain = [&](even_list &_node) {
        if (std::holds_alternative<ECons>(_node.v_)) {
          auto &_alt = std::get<ECons>(_node.v_);
          if (_alt.a1) {
            if (std::holds_alternative<typename EvenOdd::odd_list::OCons>(
                    _alt.a1->v())) {
              auto &_palt =
                  std::get<typename EvenOdd::odd_list::OCons>(_alt.a1->v_mut());
              if (_palt.a1) {
                _stack.push_back(std::move(_palt.a1));
              }
            }
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

  struct odd_list {
    // TYPES
    struct OCons {
      unsigned int a0;
      std::unique_ptr<even_list> a1;
    };

    using variant_t = std::variant<OCons>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    odd_list() {}

    explicit odd_list(OCons _v) : v_(std::move(_v)) {}

    odd_list(const odd_list &_other) : v_(std::move(_other.clone().v_)) {}

    odd_list(odd_list &&_other) : v_(std::move(_other.v_)) {}

    odd_list &operator=(const odd_list &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    odd_list &operator=(odd_list &&_other) {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    odd_list clone() const {
      const auto &[a0, a1] = std::get<OCons>(this->v());
      return odd_list(
          OCons{a0, a1 ? std::make_unique<EvenOdd::even_list>(a1->clone())
                       : nullptr});
    }

    // CREATORS
    static odd_list ocons(unsigned int a0, even_list a1) {
      return odd_list(OCons{a0, std::make_unique<even_list>(std::move(a1))});
    }

    // MANIPULATORS
    ~odd_list() {
      std::vector<std::unique_ptr<odd_list>> _stack{};
      _stack.reserve(8);
      auto _drain = [&](odd_list &_node) {
        if (std::holds_alternative<OCons>(_node.v_)) {
          auto &_alt = std::get<OCons>(_node.v_);
          if (_alt.a1) {
            if (std::holds_alternative<typename EvenOdd::even_list::ECons>(
                    _alt.a1->v())) {
              auto &_palt = std::get<typename EvenOdd::even_list::ECons>(
                  _alt.a1->v_mut());
              if (_palt.a1) {
                _stack.push_back(std::move(_palt.a1));
              }
            }
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

  static unsigned int even_length(const even_list &e);
  static unsigned int odd_length(const odd_list &o);
  static inline const even_list two =
      even_list::econs(2u, odd_list::ocons(1u, even_list::enil()));
  static inline const odd_list three = odd_list::ocons(
      3u, even_list::econs(2u, odd_list::ocons(1u, even_list::enil())));
};

const unsigned int test_even_len = EvenOdd::even_length(EvenOdd::two);
const unsigned int test_odd_len = EvenOdd::odd_length(EvenOdd::three);

#endif // INCLUDED_MUTUAL_MOD
