(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
From Crane Require Extraction.
From Crane Require Export Mapping.Std.

(** Extraction of [nat] to GMP's [mpz_class] (arbitrary-precision integers).

    This maps Peano-style [nat] to the C++ wrapper [mpz_class] from
    [<gmpxx.h>], providing unlimited precision arithmetic.

    Requirements:
    - GMP library installed with C++ bindings (libgmpxx)
    - Link with [-lgmpxx -lgmp]
*)

Crane Extract Inductive nat =>
  "mpz_class"
  [ "mpz_class(0)" "(mpz_class(%a0) + 1)" ]
  "if (%scrut <= 0) { %br0 } else { mpz_class %b1a0 = %scrut - 1; %br1 }"
  From "gmpxx.h".

Crane Extract Numeral nat => "mpz_class(%n)".

Definition zero : nat := 0.
Definition one : nat := 1.
Definition two : nat := 2.
Definition three : nat := 3.
Definition four : nat := 4.
Definition five : nat := 5.
Definition six : nat := 6.
Definition seven : nat := 7.
Definition eight : nat := 8.
Definition nine : nat := 9.
Definition ten : nat := 10.
Definition eleven : nat := 11.
Definition twelve : nat := 12.
Definition thirteen : nat := 13.
Definition fourteen : nat := 14.
Definition fifteen : nat := 15.
Definition sixteen : nat := 16.
Definition seventeen : nat := 17.
Definition eighteen : nat := 18.
Definition nineteen : nat := 19.
Definition twenty : nat := 20.
Definition twenty_one : nat := 21.
Definition twenty_two : nat := 22.
Definition twenty_three : nat := 23.
Definition twenty_four : nat := 24.
Definition twenty_five : nat := 25.
Definition twenty_six : nat := 26.
Definition twenty_seven : nat := 27.
Definition twenty_eight : nat := 28.
Definition twenty_nine : nat := 29.
Definition thirty : nat := 30.
Definition thirty_one : nat := 31.
Definition thirty_two : nat := 32.
Definition thirty_three : nat := 33.
Definition thirty_four : nat := 34.
Definition thirty_five : nat := 35.
Definition thirty_six : nat := 36.
Definition thirty_seven : nat := 37.
Definition thirty_eight : nat := 38.
Definition thirty_nine : nat := 39.
Definition forty : nat := 40.
Definition forty_one : nat := 41.
Definition forty_two : nat := 42.
Definition forty_three : nat := 43.
Definition forty_four : nat := 44.
Definition forty_five : nat := 45.
Definition forty_six : nat := 46.
Definition forty_seven : nat := 47.
Definition forty_eight : nat := 48.
Definition forty_nine : nat := 49.
Definition fifty : nat := 50.
Definition fifty_one : nat := 51.
Definition fifty_two : nat := 52.
Definition fifty_three : nat := 53.
Definition fifty_four : nat := 54.
Definition fifty_five : nat := 55.
Definition fifty_six : nat := 56.
Definition fifty_seven : nat := 57.
Definition fifty_eight : nat := 58.
Definition fifty_nine : nat := 59.
Definition sixty : nat := 60.
Definition sixty_one : nat := 61.
Definition sixty_two : nat := 62.
Definition sixty_three : nat := 63.
Definition sixty_four : nat := 64.
Definition sixty_five : nat := 65.
Definition sixty_six : nat := 66.
Definition sixty_seven : nat := 67.
Definition sixty_eight : nat := 68.
Definition sixty_nine : nat := 69.
Definition seventy : nat := 70.
Definition seventy_one : nat := 71.
Definition seventy_two : nat := 72.
Definition seventy_three : nat := 73.
Definition seventy_four : nat := 74.
Definition seventy_five : nat := 75.
Definition seventy_six : nat := 76.
Definition seventy_seven : nat := 77.
Definition seventy_eight : nat := 78.
Definition seventy_nine : nat := 79.
Definition eighty : nat := 80.
Definition eighty_one : nat := 81.
Definition eighty_two : nat := 82.
Definition eighty_three : nat := 83.
Definition eighty_four : nat := 84.
Definition eighty_five : nat := 85.
Definition eighty_six : nat := 86.
Definition eighty_seven : nat := 87.
Definition eighty_eight : nat := 88.
Definition eighty_nine : nat := 89.
Definition ninety : nat := 90.
Definition ninety_one : nat := 91.
Definition ninety_two : nat := 92.
Definition ninety_three : nat := 93.
Definition ninety_four : nat := 94.
Definition ninety_five : nat := 95.
Definition ninety_six : nat := 96.
Definition ninety_seven : nat := 97.
Definition ninety_eight : nat := 98.
Definition ninety_nine : nat := 99.
Definition one_hundred : nat := 100.
Definition one_hundred_one : nat := 101.
Definition one_hundred_two : nat := 102.
Definition one_hundred_three : nat := 103.
Definition one_hundred_four : nat := 104.
Definition one_hundred_five : nat := 105.
Definition one_hundred_six : nat := 106.
Definition one_hundred_seven : nat := 107.
Definition one_hundred_eight : nat := 108.
Definition one_hundred_nine : nat := 109.
Definition one_hundred_ten : nat := 110.
Definition one_hundred_eleven : nat := 111.
Definition one_hundred_twelve : nat := 112.
Definition one_hundred_thirteen : nat := 113.
Definition one_hundred_fourteen : nat := 114.
Definition one_hundred_fifteen : nat := 115.
Definition one_hundred_sixteen : nat := 116.
Definition one_hundred_seventeen : nat := 117.
Definition one_hundred_eighteen : nat := 118.
Definition one_hundred_nineteen : nat := 119.
Definition one_hundred_twenty : nat := 120.
Definition one_hundred_twenty_one : nat := 121.
Definition one_hundred_twenty_two : nat := 122.
Definition one_hundred_twenty_three : nat := 123.
Definition one_hundred_twenty_four : nat := 124.
Definition one_hundred_twenty_five : nat := 125.
Definition one_hundred_twenty_six : nat := 126.
Definition one_hundred_twenty_seven : nat := 127.
Definition one_hundred_twenty_eight : nat := 128.
Definition one_hundred_twenty_nine : nat := 129.
Definition one_hundred_thirty : nat := 130.
Definition one_hundred_thirty_one : nat := 131.
Definition one_hundred_thirty_two : nat := 132.
Definition one_hundred_thirty_three : nat := 133.
Definition one_hundred_thirty_four : nat := 134.
Definition one_hundred_thirty_five : nat := 135.
Definition one_hundred_thirty_six : nat := 136.
Definition one_hundred_thirty_seven : nat := 137.
Definition one_hundred_thirty_eight : nat := 138.
Definition one_hundred_thirty_nine : nat := 139.
Definition one_hundred_forty : nat := 140.
Definition one_hundred_forty_one : nat := 141.
Definition one_hundred_forty_two : nat := 142.
Definition one_hundred_forty_three : nat := 143.
Definition one_hundred_forty_four : nat := 144.
Definition one_hundred_forty_five : nat := 145.
Definition one_hundred_forty_six : nat := 146.
Definition one_hundred_forty_seven : nat := 147.
Definition one_hundred_forty_eight : nat := 148.
Definition one_hundred_forty_nine : nat := 149.
Definition one_hundred_fifty : nat := 150.

Crane Extract Inlined Constant Nat.add => "(%a0 + %a1)".
Crane Extract Inlined Constant Nat.mul => "(%a0 * %a1)".
Crane Extract Inlined Constant Nat.modulo => "(%a0 % %a1)".
Crane Extract Inlined Constant Nat.double => "(%a0 + %a0)".
Crane Extract Inlined Constant Nat.pred => "(%a0 > 0 ? %a0 - 1 : %a0)".
Crane Extract Inlined Constant Nat.sub => "(%a0 >= %a1 ? %a0 - %a1 : mpz_class(0))".
Crane Extract Inlined Constant Nat.max => "(%a0 >= %a1 ? %a0 : %a1)".
Crane Extract Inlined Constant Nat.min => "(%a0 <= %a1 ? %a0 : %a1)".
Crane Extract Inlined Constant Nat.eqb => "(%a0 == %a1)".
Crane Extract Inlined Constant Nat.ltb => "(%a0 < %a1)".
Crane Extract Inlined Constant Nat.leb => "(%a0 <= %a1)".

Crane Extract Inlined Constant Nat.one => "mpz_class(1)".
Crane Extract Inlined Constant Nat.two => "mpz_class(2)".
Crane Extract Inlined Constant zero => "mpz_class(0)".
Crane Extract Inlined Constant one => "mpz_class(1)".
Crane Extract Inlined Constant two => "mpz_class(2)".
Crane Extract Inlined Constant three => "mpz_class(3)".
Crane Extract Inlined Constant four => "mpz_class(4)".
Crane Extract Inlined Constant five => "mpz_class(5)".
Crane Extract Inlined Constant six => "mpz_class(6)".
Crane Extract Inlined Constant seven => "mpz_class(7)".
Crane Extract Inlined Constant eight => "mpz_class(8)".
Crane Extract Inlined Constant nine => "mpz_class(9)".
Crane Extract Inlined Constant ten => "mpz_class(10)".
Crane Extract Inlined Constant eleven => "mpz_class(11)".
Crane Extract Inlined Constant twelve => "mpz_class(12)".
Crane Extract Inlined Constant thirteen => "mpz_class(13)".
Crane Extract Inlined Constant fourteen => "mpz_class(14)".
Crane Extract Inlined Constant fifteen => "mpz_class(15)".
Crane Extract Inlined Constant sixteen => "mpz_class(16)".
Crane Extract Inlined Constant seventeen => "mpz_class(17)".
Crane Extract Inlined Constant eighteen => "mpz_class(18)".
Crane Extract Inlined Constant nineteen => "mpz_class(19)".
Crane Extract Inlined Constant twenty => "mpz_class(20)".
Crane Extract Inlined Constant twenty_one => "mpz_class(21)".
Crane Extract Inlined Constant twenty_two => "mpz_class(22)".
Crane Extract Inlined Constant twenty_three => "mpz_class(23)".
Crane Extract Inlined Constant twenty_four => "mpz_class(24)".
Crane Extract Inlined Constant twenty_five => "mpz_class(25)".
Crane Extract Inlined Constant twenty_six => "mpz_class(26)".
Crane Extract Inlined Constant twenty_seven => "mpz_class(27)".
Crane Extract Inlined Constant twenty_eight => "mpz_class(28)".
Crane Extract Inlined Constant twenty_nine => "mpz_class(29)".
Crane Extract Inlined Constant thirty => "mpz_class(30)".
Crane Extract Inlined Constant thirty_one => "mpz_class(31)".
Crane Extract Inlined Constant thirty_two => "mpz_class(32)".
Crane Extract Inlined Constant thirty_three => "mpz_class(33)".
Crane Extract Inlined Constant thirty_four => "mpz_class(34)".
Crane Extract Inlined Constant thirty_five => "mpz_class(35)".
Crane Extract Inlined Constant thirty_six => "mpz_class(36)".
Crane Extract Inlined Constant thirty_seven => "mpz_class(37)".
Crane Extract Inlined Constant thirty_eight => "mpz_class(38)".
Crane Extract Inlined Constant thirty_nine => "mpz_class(39)".
Crane Extract Inlined Constant forty => "mpz_class(40)".
Crane Extract Inlined Constant forty_one => "mpz_class(41)".
Crane Extract Inlined Constant forty_two => "mpz_class(42)".
Crane Extract Inlined Constant forty_three => "mpz_class(43)".
Crane Extract Inlined Constant forty_four => "mpz_class(44)".
Crane Extract Inlined Constant forty_five => "mpz_class(45)".
Crane Extract Inlined Constant forty_six => "mpz_class(46)".
Crane Extract Inlined Constant forty_seven => "mpz_class(47)".
Crane Extract Inlined Constant forty_eight => "mpz_class(48)".
Crane Extract Inlined Constant forty_nine => "mpz_class(49)".
Crane Extract Inlined Constant fifty => "mpz_class(50)".
Crane Extract Inlined Constant fifty_one => "mpz_class(51)".
Crane Extract Inlined Constant fifty_two => "mpz_class(52)".
Crane Extract Inlined Constant fifty_three => "mpz_class(53)".
Crane Extract Inlined Constant fifty_four => "mpz_class(54)".
Crane Extract Inlined Constant fifty_five => "mpz_class(55)".
Crane Extract Inlined Constant fifty_six => "mpz_class(56)".
Crane Extract Inlined Constant fifty_seven => "mpz_class(57)".
Crane Extract Inlined Constant fifty_eight => "mpz_class(58)".
Crane Extract Inlined Constant fifty_nine => "mpz_class(59)".
Crane Extract Inlined Constant sixty => "mpz_class(60)".
Crane Extract Inlined Constant sixty_one => "mpz_class(61)".
Crane Extract Inlined Constant sixty_two => "mpz_class(62)".
Crane Extract Inlined Constant sixty_three => "mpz_class(63)".
Crane Extract Inlined Constant sixty_four => "mpz_class(64)".
Crane Extract Inlined Constant sixty_five => "mpz_class(65)".
Crane Extract Inlined Constant sixty_six => "mpz_class(66)".
Crane Extract Inlined Constant sixty_seven => "mpz_class(67)".
Crane Extract Inlined Constant sixty_eight => "mpz_class(68)".
Crane Extract Inlined Constant sixty_nine => "mpz_class(69)".
Crane Extract Inlined Constant seventy => "mpz_class(70)".
Crane Extract Inlined Constant seventy_one => "mpz_class(71)".
Crane Extract Inlined Constant seventy_two => "mpz_class(72)".
Crane Extract Inlined Constant seventy_three => "mpz_class(73)".
Crane Extract Inlined Constant seventy_four => "mpz_class(74)".
Crane Extract Inlined Constant seventy_five => "mpz_class(75)".
Crane Extract Inlined Constant seventy_six => "mpz_class(76)".
Crane Extract Inlined Constant seventy_seven => "mpz_class(77)".
Crane Extract Inlined Constant seventy_eight => "mpz_class(78)".
Crane Extract Inlined Constant seventy_nine => "mpz_class(79)".
Crane Extract Inlined Constant eighty => "mpz_class(80)".
Crane Extract Inlined Constant eighty_one => "mpz_class(81)".
Crane Extract Inlined Constant eighty_two => "mpz_class(82)".
Crane Extract Inlined Constant eighty_three => "mpz_class(83)".
Crane Extract Inlined Constant eighty_four => "mpz_class(84)".
Crane Extract Inlined Constant eighty_five => "mpz_class(85)".
Crane Extract Inlined Constant eighty_six => "mpz_class(86)".
Crane Extract Inlined Constant eighty_seven => "mpz_class(87)".
Crane Extract Inlined Constant eighty_eight => "mpz_class(88)".
Crane Extract Inlined Constant eighty_nine => "mpz_class(89)".
Crane Extract Inlined Constant ninety => "mpz_class(90)".
Crane Extract Inlined Constant ninety_one => "mpz_class(91)".
Crane Extract Inlined Constant ninety_two => "mpz_class(92)".
Crane Extract Inlined Constant ninety_three => "mpz_class(93)".
Crane Extract Inlined Constant ninety_four => "mpz_class(94)".
Crane Extract Inlined Constant ninety_five => "mpz_class(95)".
Crane Extract Inlined Constant ninety_six => "mpz_class(96)".
Crane Extract Inlined Constant ninety_seven => "mpz_class(97)".
Crane Extract Inlined Constant ninety_eight => "mpz_class(98)".
Crane Extract Inlined Constant ninety_nine => "mpz_class(99)".
Crane Extract Inlined Constant one_hundred => "mpz_class(100)".
Crane Extract Inlined Constant one_hundred_one => "mpz_class(101)".
Crane Extract Inlined Constant one_hundred_two => "mpz_class(102)".
Crane Extract Inlined Constant one_hundred_three => "mpz_class(103)".
Crane Extract Inlined Constant one_hundred_four => "mpz_class(104)".
Crane Extract Inlined Constant one_hundred_five => "mpz_class(105)".
Crane Extract Inlined Constant one_hundred_six => "mpz_class(106)".
Crane Extract Inlined Constant one_hundred_seven => "mpz_class(107)".
Crane Extract Inlined Constant one_hundred_eight => "mpz_class(108)".
Crane Extract Inlined Constant one_hundred_nine => "mpz_class(109)".
Crane Extract Inlined Constant one_hundred_ten => "mpz_class(110)".
Crane Extract Inlined Constant one_hundred_eleven => "mpz_class(111)".
Crane Extract Inlined Constant one_hundred_twelve => "mpz_class(112)".
Crane Extract Inlined Constant one_hundred_thirteen => "mpz_class(113)".
Crane Extract Inlined Constant one_hundred_fourteen => "mpz_class(114)".
Crane Extract Inlined Constant one_hundred_fifteen => "mpz_class(115)".
Crane Extract Inlined Constant one_hundred_sixteen => "mpz_class(116)".
Crane Extract Inlined Constant one_hundred_seventeen => "mpz_class(117)".
Crane Extract Inlined Constant one_hundred_eighteen => "mpz_class(118)".
Crane Extract Inlined Constant one_hundred_nineteen => "mpz_class(119)".
Crane Extract Inlined Constant one_hundred_twenty => "mpz_class(120)".
Crane Extract Inlined Constant one_hundred_twenty_one => "mpz_class(121)".
Crane Extract Inlined Constant one_hundred_twenty_two => "mpz_class(122)".
Crane Extract Inlined Constant one_hundred_twenty_three => "mpz_class(123)".
Crane Extract Inlined Constant one_hundred_twenty_four => "mpz_class(124)".
Crane Extract Inlined Constant one_hundred_twenty_five => "mpz_class(125)".
Crane Extract Inlined Constant one_hundred_twenty_six => "mpz_class(126)".
Crane Extract Inlined Constant one_hundred_twenty_seven => "mpz_class(127)".
Crane Extract Inlined Constant one_hundred_twenty_eight => "mpz_class(128)".
Crane Extract Inlined Constant one_hundred_twenty_nine => "mpz_class(129)".
Crane Extract Inlined Constant one_hundred_thirty => "mpz_class(130)".
Crane Extract Inlined Constant one_hundred_thirty_one => "mpz_class(131)".
Crane Extract Inlined Constant one_hundred_thirty_two => "mpz_class(132)".
Crane Extract Inlined Constant one_hundred_thirty_three => "mpz_class(133)".
Crane Extract Inlined Constant one_hundred_thirty_four => "mpz_class(134)".
Crane Extract Inlined Constant one_hundred_thirty_five => "mpz_class(135)".
Crane Extract Inlined Constant one_hundred_thirty_six => "mpz_class(136)".
Crane Extract Inlined Constant one_hundred_thirty_seven => "mpz_class(137)".
Crane Extract Inlined Constant one_hundred_thirty_eight => "mpz_class(138)".
Crane Extract Inlined Constant one_hundred_thirty_nine => "mpz_class(139)".
Crane Extract Inlined Constant one_hundred_forty => "mpz_class(140)".
Crane Extract Inlined Constant one_hundred_forty_one => "mpz_class(141)".
Crane Extract Inlined Constant one_hundred_forty_two => "mpz_class(142)".
Crane Extract Inlined Constant one_hundred_forty_three => "mpz_class(143)".
Crane Extract Inlined Constant one_hundred_forty_four => "mpz_class(144)".
Crane Extract Inlined Constant one_hundred_forty_five => "mpz_class(145)".
Crane Extract Inlined Constant one_hundred_forty_six => "mpz_class(146)".
Crane Extract Inlined Constant one_hundred_forty_seven => "mpz_class(147)".
Crane Extract Inlined Constant one_hundred_forty_eight => "mpz_class(148)".
Crane Extract Inlined Constant one_hundred_forty_nine => "mpz_class(149)".
Crane Extract Inlined Constant one_hundred_fifty => "mpz_class(150)".

From Corelib Require Import PrimInt63.
Axiom nat_of_int : int -> nat.
Crane Extract Inlined Constant nat_of_int => "mpz_class(%a0)".

From Corelib Require Import PrimString.
Axiom string_of_nat : nat -> string.
Crane Extract Inlined Constant string_of_nat => "%a0.get_str()".
