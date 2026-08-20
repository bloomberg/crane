#include "object_model.h"

std::pair<std::pair<int64_t, int64_t>, int64_t> testtoST1_ext() {
  Point<std::monostate> p = []() {
    std::shared_ptr<int64_t> ref;
    ref = std::make_shared<decltype(INT64_C(1))>(INT64_C(1));
    return Point<std::monostate>{
        [=](std::monostate) mutable { return *ref; },
        [=](int64_t move_amt) mutable {
          int64_t i = *ref;
          *ref = static_cast<int64_t>(static_cast<uint64_t>(i) +
                                      static_cast<uint64_t>(move_amt));
          return std::monostate{};
        },
        [=](std::monostate) mutable {
          int64_t i = *ref;
          return static_cast<int64_t>(static_cast<uint64_t>(i) -
                                      static_cast<uint64_t>(INT64_C(1)));
        }};
  }();
  int64_t a = p.getX(std::monostate{});
  p.moveD(INT64_C(2));
  int64_t b = p.getX(std::monostate{});
  int64_t c = p.offsetX(std::monostate{});
  return std::make_pair(std::make_pair(a, b), c);
}

std::pair<std::pair<std::pair<int64_t, int64_t>, int64_t>, int64_t>
testtoST2_ext() {
  Point<std::monostate> p1 = []() {
    std::shared_ptr<int64_t> ref;
    ref = std::make_shared<decltype(INT64_C(1))>(INT64_C(1));
    return Point<std::monostate>{
        [=](std::monostate) mutable { return *ref; },
        [=](int64_t move_amt) mutable {
          int64_t i = *ref;
          *ref = static_cast<int64_t>(static_cast<uint64_t>(i) +
                                      static_cast<uint64_t>(move_amt));
          return std::monostate{};
        },
        [=](std::monostate) mutable {
          int64_t i = *ref;
          return static_cast<int64_t>(static_cast<uint64_t>(i) -
                                      static_cast<uint64_t>(INT64_C(1)));
        }};
  }();
  Point<std::monostate> p2 = []() {
    std::shared_ptr<int64_t> ref;
    ref = std::make_shared<decltype(INT64_C(10))>(INT64_C(10));
    return Point<std::monostate>{
        [=](std::monostate) mutable { return *ref; },
        [=](int64_t move_amt) mutable {
          int64_t i = *ref;
          *ref = static_cast<int64_t>(static_cast<uint64_t>(i) +
                                      static_cast<uint64_t>(move_amt));
          return std::monostate{};
        },
        [=](std::monostate) mutable {
          int64_t i = *ref;
          return static_cast<int64_t>(static_cast<uint64_t>(i) -
                                      static_cast<uint64_t>(INT64_C(10)));
        }};
  }();
  int64_t a = p1.getX(std::monostate{});
  int64_t b = p2.getX(std::monostate{});
  int64_t v1 = p1.getX(std::monostate{});
  p2.moveD(v1);
  int64_t c = p1.getX(std::monostate{});
  int64_t d = p2.getX(std::monostate{});
  return std::make_pair(std::make_pair(std::make_pair(a, b), c), d);
}

std::pair<std::pair<std::pair<int64_t, int64_t>, bool>, int64_t>
acc_test1_ext() {
  Account<std::monostate> acc = []() {
    std::shared_ptr<int64_t> bal_ref;
    bal_ref = std::make_shared<decltype(INT64_C(100))>(INT64_C(100));
    return Account<std::monostate>{
        [=](std::monostate) mutable { return *bal_ref; },
        [=](uint64_t amt) mutable {
          int64_t bal = *bal_ref;
          *bal_ref = static_cast<int64_t>(
              static_cast<uint64_t>(bal) +
              static_cast<uint64_t>(static_cast<int64_t>(amt)));
          return static_cast<int64_t>(
              static_cast<uint64_t>(bal) +
              static_cast<uint64_t>(static_cast<int64_t>(amt)));
        },
        [=](int64_t amt) mutable {
          int64_t bal = *bal_ref;
          if (static_cast<int64_t>(static_cast<uint64_t>(bal) -
                                   static_cast<uint64_t>(amt)) < INT64_C(0)) {
            return std::optional<int64_t>();
          } else {
            *bal_ref = static_cast<int64_t>(static_cast<uint64_t>(bal) -
                                            static_cast<uint64_t>(amt));
            return std::make_optional<int64_t>(static_cast<int64_t>(
                static_cast<uint64_t>(bal) - static_cast<uint64_t>(amt)));
          }
        }};
  }();
  int64_t a = acc.getBalance(std::monostate{});
  int64_t b = acc.deposit(UINT64_C(50));
  std::optional<int64_t> c = acc.withdraw(INT64_C(160));
  int64_t d = acc.getBalance(std::monostate{});
  return std::make_pair(std::make_pair(std::make_pair(a, b),
                                       [=]() mutable -> bool {
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
  Account<std::monostate> acc1 = []() {
    std::shared_ptr<int64_t> bal_ref;
    bal_ref = std::make_shared<decltype(INT64_C(100))>(INT64_C(100));
    return Account<std::monostate>{
        [=](std::monostate) mutable { return *bal_ref; },
        [=](uint64_t amt) mutable {
          int64_t bal = *bal_ref;
          *bal_ref = static_cast<int64_t>(
              static_cast<uint64_t>(bal) +
              static_cast<uint64_t>(static_cast<int64_t>(amt)));
          return static_cast<int64_t>(
              static_cast<uint64_t>(bal) +
              static_cast<uint64_t>(static_cast<int64_t>(amt)));
        },
        [=](int64_t amt) mutable {
          int64_t bal = *bal_ref;
          if (static_cast<int64_t>(static_cast<uint64_t>(bal) -
                                   static_cast<uint64_t>(amt)) < INT64_C(0)) {
            return std::optional<int64_t>();
          } else {
            *bal_ref = static_cast<int64_t>(static_cast<uint64_t>(bal) -
                                            static_cast<uint64_t>(amt));
            return std::make_optional<int64_t>(static_cast<int64_t>(
                static_cast<uint64_t>(bal) - static_cast<uint64_t>(amt)));
          }
        }};
  }();
  Account<std::monostate> acc2 = []() {
    std::shared_ptr<int64_t> bal_ref;
    bal_ref = std::make_shared<decltype(INT64_C(150))>(INT64_C(150));
    return Account<std::monostate>{
        [=](std::monostate) mutable { return *bal_ref; },
        [=](uint64_t amt) mutable {
          int64_t bal = *bal_ref;
          *bal_ref = static_cast<int64_t>(
              static_cast<uint64_t>(bal) +
              static_cast<uint64_t>(static_cast<int64_t>(amt)));
          return static_cast<int64_t>(
              static_cast<uint64_t>(bal) +
              static_cast<uint64_t>(static_cast<int64_t>(amt)));
        },
        [=](int64_t amt) mutable {
          int64_t bal = *bal_ref;
          if (static_cast<int64_t>(static_cast<uint64_t>(bal) -
                                   static_cast<uint64_t>(amt)) < INT64_C(0)) {
            return std::optional<int64_t>();
          } else {
            *bal_ref = static_cast<int64_t>(static_cast<uint64_t>(bal) -
                                            static_cast<uint64_t>(amt));
            return std::make_optional<int64_t>(static_cast<int64_t>(
                static_cast<uint64_t>(bal) - static_cast<uint64_t>(amt)));
          }
        }};
  }();
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
  BankAccountCollection<std::monostate> acc = []() {
    Account<std::monostate> checking_ = []() {
      std::shared_ptr<int64_t> bal_ref;
      bal_ref = std::make_shared<decltype(INT64_C(100))>(INT64_C(100));
      return Account<std::monostate>{
          [=](std::monostate) mutable { return *bal_ref; },
          [=](uint64_t amt) mutable {
            int64_t bal = *bal_ref;
            *bal_ref = static_cast<int64_t>(
                static_cast<uint64_t>(bal) +
                static_cast<uint64_t>(static_cast<int64_t>(amt)));
            return static_cast<int64_t>(
                static_cast<uint64_t>(bal) +
                static_cast<uint64_t>(static_cast<int64_t>(amt)));
          },
          [=](int64_t amt) mutable {
            int64_t bal = *bal_ref;
            if (static_cast<int64_t>(static_cast<uint64_t>(bal) -
                                     static_cast<uint64_t>(amt)) < INT64_C(0)) {
              return std::optional<int64_t>();
            } else {
              *bal_ref = static_cast<int64_t>(static_cast<uint64_t>(bal) -
                                              static_cast<uint64_t>(amt));
              return std::make_optional<int64_t>(static_cast<int64_t>(
                  static_cast<uint64_t>(bal) - static_cast<uint64_t>(amt)));
            }
          }};
    }();
    Account<std::monostate> saving_ = []() {
      std::shared_ptr<int64_t> bal_ref;
      bal_ref = std::make_shared<decltype(INT64_C(150))>(INT64_C(150));
      return Account<std::monostate>{
          [=](std::monostate) mutable { return *bal_ref; },
          [=](uint64_t amt) mutable {
            int64_t bal = *bal_ref;
            *bal_ref = static_cast<int64_t>(
                static_cast<uint64_t>(bal) +
                static_cast<uint64_t>(static_cast<int64_t>(amt)));
            return static_cast<int64_t>(
                static_cast<uint64_t>(bal) +
                static_cast<uint64_t>(static_cast<int64_t>(amt)));
          },
          [=](int64_t amt) mutable {
            int64_t bal = *bal_ref;
            if (static_cast<int64_t>(static_cast<uint64_t>(bal) -
                                     static_cast<uint64_t>(amt)) < INT64_C(0)) {
              return std::optional<int64_t>();
            } else {
              *bal_ref = static_cast<int64_t>(static_cast<uint64_t>(bal) -
                                              static_cast<uint64_t>(amt));
              return std::make_optional<int64_t>(static_cast<int64_t>(
                  static_cast<uint64_t>(bal) - static_cast<uint64_t>(amt)));
            }
          }};
    }();
    return BankAccountCollection<std::monostate>{checking_, saving_};
  }();
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
