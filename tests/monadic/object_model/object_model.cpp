#include "object_model.h"

std::pair<std::pair<int64_t, int64_t>, int64_t> testtoST1_ext() {
  std::shared_ptr<int64_t> _lc1_ref;
  _lc1_ref = std::make_shared<decltype(INT64_C(1))>(INT64_C(1));
  int64_t a = *_lc1_ref;
  int64_t _lc2_move_amt = INT64_C(2);
  int64_t _lc2_i = *_lc1_ref;
  *_lc1_ref = static_cast<int64_t>(static_cast<uint64_t>(_lc2_i) +
                                   static_cast<uint64_t>(_lc2_move_amt));
  int64_t b = *_lc1_ref;
  int64_t _lc3_i = *_lc1_ref;
  int64_t c = static_cast<int64_t>(static_cast<uint64_t>(_lc3_i) -
                                   static_cast<uint64_t>(INT64_C(1)));
  return std::make_pair(std::make_pair(a, b), c);
}

std::pair<std::pair<std::pair<int64_t, int64_t>, int64_t>, int64_t>
testtoST2_ext() {
  std::shared_ptr<int64_t> _lc1_ref;
  _lc1_ref = std::make_shared<decltype(INT64_C(1))>(INT64_C(1));
  std::shared_ptr<int64_t> _lc2_ref;
  _lc2_ref = std::make_shared<decltype(INT64_C(10))>(INT64_C(10));
  int64_t a = *_lc1_ref;
  int64_t b = *_lc2_ref;
  int64_t v1 = *_lc1_ref;
  int64_t _lc3_move_amt = v1;
  int64_t _lc3_i = *_lc2_ref;
  *_lc2_ref = static_cast<int64_t>(static_cast<uint64_t>(_lc3_i) +
                                   static_cast<uint64_t>(_lc3_move_amt));
  int64_t c = *_lc1_ref;
  int64_t d = *_lc2_ref;
  return std::make_pair(std::make_pair(std::make_pair(a, b), c), d);
}

std::pair<std::pair<std::pair<int64_t, int64_t>, bool>, int64_t>
acc_test1_ext() {
  std::shared_ptr<int64_t> _lc1_bal_ref;
  _lc1_bal_ref = std::make_shared<decltype(INT64_C(100))>(INT64_C(100));
  Account<std::monostate> acc = Account<std::monostate>{
      [=](std::monostate) { return *_lc1_bal_ref; },
      [=](uint64_t amt) {
        int64_t bal = *_lc1_bal_ref;
        *_lc1_bal_ref = static_cast<int64_t>(
            static_cast<uint64_t>(bal) +
            static_cast<uint64_t>(static_cast<int64_t>(amt)));
        return static_cast<int64_t>(
            static_cast<uint64_t>(bal) +
            static_cast<uint64_t>(static_cast<int64_t>(amt)));
      },
      [=](int64_t amt) {
        int64_t bal = *_lc1_bal_ref;
        if (static_cast<int64_t>(static_cast<uint64_t>(bal) -
                                 static_cast<uint64_t>(amt)) < INT64_C(0)) {
          return std::optional<int64_t>();
        } else {
          *_lc1_bal_ref = static_cast<int64_t>(static_cast<uint64_t>(bal) -
                                               static_cast<uint64_t>(amt));
          return std::make_optional<int64_t>(static_cast<int64_t>(
              static_cast<uint64_t>(bal) - static_cast<uint64_t>(amt)));
        }
      }};
  int64_t a = acc.getBalance(std::monostate{});
  int64_t b = acc.deposit(UINT64_C(50));
  std::optional<int64_t> c = acc.withdraw(INT64_C(160));
  int64_t d = acc.getBalance(std::monostate{});
  return std::make_pair(std::make_pair(std::make_pair(a, b),
                                       [&]() -> bool {
                                         if (c.has_value()) {
                                           const int64_t &_x = *c;
                                           return true;
                                         } else {
                                           return false;
                                         }
                                       }()),
                        d);
}

std::pair<std::pair<std::pair<int64_t, bool>, int64_t>, int64_t>
acc_test2_ext() {
  std::shared_ptr<int64_t> _lc1_bal_ref;
  _lc1_bal_ref = std::make_shared<decltype(INT64_C(100))>(INT64_C(100));
  Account<std::monostate> acc1 = Account<std::monostate>{
      [=](std::monostate) { return *_lc1_bal_ref; },
      [=](uint64_t amt) {
        int64_t bal = *_lc1_bal_ref;
        *_lc1_bal_ref = static_cast<int64_t>(
            static_cast<uint64_t>(bal) +
            static_cast<uint64_t>(static_cast<int64_t>(amt)));
        return static_cast<int64_t>(
            static_cast<uint64_t>(bal) +
            static_cast<uint64_t>(static_cast<int64_t>(amt)));
      },
      [=](int64_t amt) {
        int64_t bal = *_lc1_bal_ref;
        if (static_cast<int64_t>(static_cast<uint64_t>(bal) -
                                 static_cast<uint64_t>(amt)) < INT64_C(0)) {
          return std::optional<int64_t>();
        } else {
          *_lc1_bal_ref = static_cast<int64_t>(static_cast<uint64_t>(bal) -
                                               static_cast<uint64_t>(amt));
          return std::make_optional<int64_t>(static_cast<int64_t>(
              static_cast<uint64_t>(bal) - static_cast<uint64_t>(amt)));
        }
      }};
  std::shared_ptr<int64_t> _lc2_bal_ref;
  _lc2_bal_ref = std::make_shared<decltype(INT64_C(150))>(INT64_C(150));
  Account<std::monostate> acc2 = Account<std::monostate>{
      [=](std::monostate) { return *_lc2_bal_ref; },
      [=](uint64_t amt) {
        int64_t bal = *_lc2_bal_ref;
        *_lc2_bal_ref = static_cast<int64_t>(
            static_cast<uint64_t>(bal) +
            static_cast<uint64_t>(static_cast<int64_t>(amt)));
        return static_cast<int64_t>(
            static_cast<uint64_t>(bal) +
            static_cast<uint64_t>(static_cast<int64_t>(amt)));
      },
      [=](int64_t amt) {
        int64_t bal = *_lc2_bal_ref;
        if (static_cast<int64_t>(static_cast<uint64_t>(bal) -
                                 static_cast<uint64_t>(amt)) < INT64_C(0)) {
          return std::optional<int64_t>();
        } else {
          *_lc2_bal_ref = static_cast<int64_t>(static_cast<uint64_t>(bal) -
                                               static_cast<uint64_t>(amt));
          return std::make_optional<int64_t>(static_cast<int64_t>(
              static_cast<uint64_t>(bal) - static_cast<uint64_t>(amt)));
        }
      }};
  int64_t a = acc1.getBalance(std::monostate{});
  std::optional<int64_t> result = acc1.withdraw(a);
  if (result.has_value()) {
    const int64_t &z = *result;
    if (z == 0) {
      int64_t b = std::move(acc2).deposit(static_cast<uint64_t>(a < 0 ? 0 : a));
      int64_t c = std::move(acc1).getBalance(std::monostate{});
      return std::make_pair(std::make_pair(std::make_pair(a, true), b), c);
    } else if (z > 0) {
      unsigned int _x = static_cast<unsigned int>(z);
      int64_t b = std::move(acc2).getBalance(std::monostate{});
      int64_t c = std::move(acc1).getBalance(std::monostate{});
      return std::make_pair(std::make_pair(std::make_pair(a, false), b), c);
    } else {
      unsigned int _x = static_cast<unsigned int>(-z);
      int64_t b = std::move(acc2).getBalance(std::monostate{});
      int64_t c = std::move(acc1).getBalance(std::monostate{});
      return std::make_pair(std::make_pair(std::make_pair(a, false), b), c);
    }
  } else {
    int64_t b = std::move(acc2).getBalance(std::monostate{});
    int64_t c = std::move(acc1).getBalance(std::monostate{});
    return std::make_pair(std::make_pair(std::make_pair(a, false), b), c);
  }
}

std::pair<std::pair<std::pair<int64_t, bool>, int64_t>, int64_t>
bankacc_test1_ext() {
  std::shared_ptr<int64_t> _lc2_bal_ref;
  _lc2_bal_ref = std::make_shared<decltype(INT64_C(100))>(INT64_C(100));
  Account<std::monostate> _lc1_checking_ = Account<std::monostate>{
      [=](std::monostate) { return *_lc2_bal_ref; },
      [=](uint64_t amt) {
        int64_t bal = *_lc2_bal_ref;
        *_lc2_bal_ref = static_cast<int64_t>(
            static_cast<uint64_t>(bal) +
            static_cast<uint64_t>(static_cast<int64_t>(amt)));
        return static_cast<int64_t>(
            static_cast<uint64_t>(bal) +
            static_cast<uint64_t>(static_cast<int64_t>(amt)));
      },
      [=](int64_t amt) {
        int64_t bal = *_lc2_bal_ref;
        if (static_cast<int64_t>(static_cast<uint64_t>(bal) -
                                 static_cast<uint64_t>(amt)) < INT64_C(0)) {
          return std::optional<int64_t>();
        } else {
          *_lc2_bal_ref = static_cast<int64_t>(static_cast<uint64_t>(bal) -
                                               static_cast<uint64_t>(amt));
          return std::make_optional<int64_t>(static_cast<int64_t>(
              static_cast<uint64_t>(bal) - static_cast<uint64_t>(amt)));
        }
      }};
  std::shared_ptr<int64_t> _lc3_bal_ref;
  _lc3_bal_ref = std::make_shared<decltype(INT64_C(150))>(INT64_C(150));
  Account<std::monostate> _lc1_saving_ = Account<std::monostate>{
      [=](std::monostate) { return *_lc3_bal_ref; },
      [=](uint64_t amt) {
        int64_t bal = *_lc3_bal_ref;
        *_lc3_bal_ref = static_cast<int64_t>(
            static_cast<uint64_t>(bal) +
            static_cast<uint64_t>(static_cast<int64_t>(amt)));
        return static_cast<int64_t>(
            static_cast<uint64_t>(bal) +
            static_cast<uint64_t>(static_cast<int64_t>(amt)));
      },
      [=](int64_t amt) {
        int64_t bal = *_lc3_bal_ref;
        if (static_cast<int64_t>(static_cast<uint64_t>(bal) -
                                 static_cast<uint64_t>(amt)) < INT64_C(0)) {
          return std::optional<int64_t>();
        } else {
          *_lc3_bal_ref = static_cast<int64_t>(static_cast<uint64_t>(bal) -
                                               static_cast<uint64_t>(amt));
          return std::make_optional<int64_t>(static_cast<int64_t>(
              static_cast<uint64_t>(bal) - static_cast<uint64_t>(amt)));
        }
      }};
  BankAccountCollection<std::monostate> acc =
      BankAccountCollection<std::monostate>{std::move(_lc1_checking_),
                                            std::move(_lc1_saving_)};
  int64_t a = acc.checking.getBalance(std::monostate{});
  std::optional<int64_t> result = acc.checking.withdraw(a);
  if (result.has_value()) {
    const int64_t &z = *result;
    if (z == 0) {
      int64_t b = acc.saving.deposit(static_cast<uint64_t>(a < 0 ? 0 : a));
      int64_t c = acc.checking.getBalance(std::monostate{});
      return std::make_pair(std::make_pair(std::make_pair(a, true), b), c);
    } else if (z > 0) {
      unsigned int _x = static_cast<unsigned int>(z);
      int64_t b = acc.checking.getBalance(std::monostate{});
      int64_t c = acc.saving.getBalance(std::monostate{});
      return std::make_pair(std::make_pair(std::make_pair(a, false), b), c);
    } else {
      unsigned int _x = static_cast<unsigned int>(-z);
      int64_t b = acc.checking.getBalance(std::monostate{});
      int64_t c = acc.saving.getBalance(std::monostate{});
      return std::make_pair(std::make_pair(std::make_pair(a, false), b), c);
    }
  } else {
    int64_t b = acc.checking.getBalance(std::monostate{});
    int64_t c = acc.saving.getBalance(std::monostate{});
    return std::make_pair(std::make_pair(std::make_pair(a, false), b), c);
  }
}

List<uint64_t> ListDef::seq(uint64_t start, uint64_t len) {
  if (len <= 0) {
    return List<uint64_t>::nil();
  } else {
    uint64_t len0 = len - 1;
    return List<uint64_t>::cons(start, ListDef::seq((start + 1), len0));
  }
}
