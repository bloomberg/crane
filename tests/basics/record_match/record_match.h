#ifndef INCLUDED_RECORD_MATCH
#define INCLUDED_RECORD_MATCH

struct RecordMatch {
  struct MyRec {
    uint64_t f1;
    uint64_t f2;
    uint64_t f3;

    // ACCESSORS
    MyRec clone() const { return MyRec{this->f1, this->f2, this->f3}; }
  };

  static uint64_t sum(const MyRec &r);
};

#endif // INCLUDED_RECORD_MATCH
