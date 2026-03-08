(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
From Crane Require Extraction.
From Crane Require Export Mapping.Std.

(** Disclaimer: trying to obtain efficient certified programs
    by extracting [nat] into [int] is definitively *not* a good idea:

    - This is just a syntactic adaptation, many things can go wrong,
    such as name captures.

    - Since [int] is bounded while [nat] is (theoretically) infinite,
    you have to make sure by yourself that your program will not
    manipulate numbers greater than [max_int]. Otherwise you should
    consider the translation of [nat] into [big_int].

    - Moreover, the mere translation of [nat] into [int] does not
    change the complexity of functions. For instance, [mult] stays
    quadratic. To mitigate this, we propose here a few efficient (but
    uncertified) realizers for some common functions over [nat].

    This file is hence provided mainly for testing / prototyping
    purpose. For serious use of numbers in extracted programs,
    you are advised to use either Rocq advanced representations
    (positive, Z, N, BigN, BigZ) or modular/axiomatic representation.
*)

Crane Extract Inductive nat =>
  "unsigned int"
  [ "0" "(%a0 + 1)" ]
  "if (%scrut <= 0) { %br0 } else { unsigned int %b1a0 = %scrut - 1; %br1 }".

Crane Extract Numeral nat => "%nu".

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
Crane Extract Inlined Constant Nat.pred => "(%a0 ? %a0 - 1 : %a0)".
Crane Extract Inlined Constant Nat.sub => "(((%a0 - %a1) > %a0 ? 0 : (%a0 - %a1)))".
Crane Extract Inlined Constant Nat.max => "std::max(%a0, %a1)" From "algorithm".
Crane Extract Inlined Constant Nat.min => "std::min(%a0, %a1)" From "algorithm".
Crane Extract Inlined Constant Nat.eqb => "(%a0 == %a1)".
Crane Extract Inlined Constant Nat.ltb => "(%a0 < %a1)".
Crane Extract Inlined Constant Nat.leb => "(%a0 <= %a1)".

Crane Extract Inlined Constant Nat.one => "1u".
Crane Extract Inlined Constant Nat.two => "2u".
Crane Extract Inlined Constant zero => "0u".
Crane Extract Inlined Constant one => "1u".
Crane Extract Inlined Constant two => "2u".
Crane Extract Inlined Constant three => "3u".
Crane Extract Inlined Constant four => "4u".
Crane Extract Inlined Constant five => "5u".
Crane Extract Inlined Constant six => "6u".
Crane Extract Inlined Constant seven => "7u".
Crane Extract Inlined Constant eight => "8u".
Crane Extract Inlined Constant nine => "9u".
Crane Extract Inlined Constant ten => "10u".
Crane Extract Inlined Constant eleven => "11u".
Crane Extract Inlined Constant twelve => "12u".
Crane Extract Inlined Constant thirteen => "13u".
Crane Extract Inlined Constant fourteen => "14u".
Crane Extract Inlined Constant fifteen => "15u".
Crane Extract Inlined Constant sixteen => "16u".
Crane Extract Inlined Constant seventeen => "17u".
Crane Extract Inlined Constant eighteen => "18u".
Crane Extract Inlined Constant nineteen => "19u".
Crane Extract Inlined Constant twenty => "20u".
Crane Extract Inlined Constant twenty_one => "21u".
Crane Extract Inlined Constant twenty_two => "22u".
Crane Extract Inlined Constant twenty_three => "23u".
Crane Extract Inlined Constant twenty_four => "24u".
Crane Extract Inlined Constant twenty_five => "25u".
Crane Extract Inlined Constant twenty_six => "26u".
Crane Extract Inlined Constant twenty_seven => "27u".
Crane Extract Inlined Constant twenty_eight => "28u".
Crane Extract Inlined Constant twenty_nine => "29u".
Crane Extract Inlined Constant thirty => "30u".
Crane Extract Inlined Constant thirty_one => "31u".
Crane Extract Inlined Constant thirty_two => "32u".
Crane Extract Inlined Constant thirty_three => "33u".
Crane Extract Inlined Constant thirty_four => "34u".
Crane Extract Inlined Constant thirty_five => "35u".
Crane Extract Inlined Constant thirty_six => "36u".
Crane Extract Inlined Constant thirty_seven => "37u".
Crane Extract Inlined Constant thirty_eight => "38u".
Crane Extract Inlined Constant thirty_nine => "39u".
Crane Extract Inlined Constant forty => "40u".
Crane Extract Inlined Constant forty_one => "41u".
Crane Extract Inlined Constant forty_two => "42u".
Crane Extract Inlined Constant forty_three => "43u".
Crane Extract Inlined Constant forty_four => "44u".
Crane Extract Inlined Constant forty_five => "45u".
Crane Extract Inlined Constant forty_six => "46u".
Crane Extract Inlined Constant forty_seven => "47u".
Crane Extract Inlined Constant forty_eight => "48u".
Crane Extract Inlined Constant forty_nine => "49u".
Crane Extract Inlined Constant fifty => "50u".
Crane Extract Inlined Constant fifty_one => "51u".
Crane Extract Inlined Constant fifty_two => "52u".
Crane Extract Inlined Constant fifty_three => "53u".
Crane Extract Inlined Constant fifty_four => "54u".
Crane Extract Inlined Constant fifty_five => "55u".
Crane Extract Inlined Constant fifty_six => "56u".
Crane Extract Inlined Constant fifty_seven => "57u".
Crane Extract Inlined Constant fifty_eight => "58u".
Crane Extract Inlined Constant fifty_nine => "59u".
Crane Extract Inlined Constant sixty => "60u".
Crane Extract Inlined Constant sixty_one => "61u".
Crane Extract Inlined Constant sixty_two => "62u".
Crane Extract Inlined Constant sixty_three => "63u".
Crane Extract Inlined Constant sixty_four => "64u".
Crane Extract Inlined Constant sixty_five => "65u".
Crane Extract Inlined Constant sixty_six => "66u".
Crane Extract Inlined Constant sixty_seven => "67u".
Crane Extract Inlined Constant sixty_eight => "68u".
Crane Extract Inlined Constant sixty_nine => "69u".
Crane Extract Inlined Constant seventy => "70u".
Crane Extract Inlined Constant seventy_one => "71u".
Crane Extract Inlined Constant seventy_two => "72u".
Crane Extract Inlined Constant seventy_three => "73u".
Crane Extract Inlined Constant seventy_four => "74u".
Crane Extract Inlined Constant seventy_five => "75u".
Crane Extract Inlined Constant seventy_six => "76u".
Crane Extract Inlined Constant seventy_seven => "77u".
Crane Extract Inlined Constant seventy_eight => "78u".
Crane Extract Inlined Constant seventy_nine => "79u".
Crane Extract Inlined Constant eighty => "80u".
Crane Extract Inlined Constant eighty_one => "81u".
Crane Extract Inlined Constant eighty_two => "82u".
Crane Extract Inlined Constant eighty_three => "83u".
Crane Extract Inlined Constant eighty_four => "84u".
Crane Extract Inlined Constant eighty_five => "85u".
Crane Extract Inlined Constant eighty_six => "86u".
Crane Extract Inlined Constant eighty_seven => "87u".
Crane Extract Inlined Constant eighty_eight => "88u".
Crane Extract Inlined Constant eighty_nine => "89u".
Crane Extract Inlined Constant ninety => "90u".
Crane Extract Inlined Constant ninety_one => "91u".
Crane Extract Inlined Constant ninety_two => "92u".
Crane Extract Inlined Constant ninety_three => "93u".
Crane Extract Inlined Constant ninety_four => "94u".
Crane Extract Inlined Constant ninety_five => "95u".
Crane Extract Inlined Constant ninety_six => "96u".
Crane Extract Inlined Constant ninety_seven => "97u".
Crane Extract Inlined Constant ninety_eight => "98u".
Crane Extract Inlined Constant ninety_nine => "99u".
Crane Extract Inlined Constant one_hundred => "100u".
Crane Extract Inlined Constant one_hundred_one => "101u".
Crane Extract Inlined Constant one_hundred_two => "102u".
Crane Extract Inlined Constant one_hundred_three => "103u".
Crane Extract Inlined Constant one_hundred_four => "104u".
Crane Extract Inlined Constant one_hundred_five => "105u".
Crane Extract Inlined Constant one_hundred_six => "106u".
Crane Extract Inlined Constant one_hundred_seven => "107u".
Crane Extract Inlined Constant one_hundred_eight => "108u".
Crane Extract Inlined Constant one_hundred_nine => "109u".
Crane Extract Inlined Constant one_hundred_ten => "110u".
Crane Extract Inlined Constant one_hundred_eleven => "111u".
Crane Extract Inlined Constant one_hundred_twelve => "112u".
Crane Extract Inlined Constant one_hundred_thirteen => "113u".
Crane Extract Inlined Constant one_hundred_fourteen => "114u".
Crane Extract Inlined Constant one_hundred_fifteen => "115u".
Crane Extract Inlined Constant one_hundred_sixteen => "116u".
Crane Extract Inlined Constant one_hundred_seventeen => "117u".
Crane Extract Inlined Constant one_hundred_eighteen => "118u".
Crane Extract Inlined Constant one_hundred_nineteen => "119u".
Crane Extract Inlined Constant one_hundred_twenty => "120u".
Crane Extract Inlined Constant one_hundred_twenty_one => "121u".
Crane Extract Inlined Constant one_hundred_twenty_two => "122u".
Crane Extract Inlined Constant one_hundred_twenty_three => "123u".
Crane Extract Inlined Constant one_hundred_twenty_four => "124u".
Crane Extract Inlined Constant one_hundred_twenty_five => "125u".
Crane Extract Inlined Constant one_hundred_twenty_six => "126u".
Crane Extract Inlined Constant one_hundred_twenty_seven => "127u".
Crane Extract Inlined Constant one_hundred_twenty_eight => "128u".
Crane Extract Inlined Constant one_hundred_twenty_nine => "129u".
Crane Extract Inlined Constant one_hundred_thirty => "130u".
Crane Extract Inlined Constant one_hundred_thirty_one => "131u".
Crane Extract Inlined Constant one_hundred_thirty_two => "132u".
Crane Extract Inlined Constant one_hundred_thirty_three => "133u".
Crane Extract Inlined Constant one_hundred_thirty_four => "134u".
Crane Extract Inlined Constant one_hundred_thirty_five => "135u".
Crane Extract Inlined Constant one_hundred_thirty_six => "136u".
Crane Extract Inlined Constant one_hundred_thirty_seven => "137u".
Crane Extract Inlined Constant one_hundred_thirty_eight => "138u".
Crane Extract Inlined Constant one_hundred_thirty_nine => "139u".
Crane Extract Inlined Constant one_hundred_forty => "140u".
Crane Extract Inlined Constant one_hundred_forty_one => "141u".
Crane Extract Inlined Constant one_hundred_forty_two => "142u".
Crane Extract Inlined Constant one_hundred_forty_three => "143u".
Crane Extract Inlined Constant one_hundred_forty_four => "144u".
Crane Extract Inlined Constant one_hundred_forty_five => "145u".
Crane Extract Inlined Constant one_hundred_forty_six => "146u".
Crane Extract Inlined Constant one_hundred_forty_seven => "147u".
Crane Extract Inlined Constant one_hundred_forty_eight => "148u".
Crane Extract Inlined Constant one_hundred_forty_nine => "149u".
Crane Extract Inlined Constant one_hundred_fifty => "150u".

From Corelib Require Import PrimInt63.
Axiom nat_of_int : int -> nat.
Crane Extract Inlined Constant nat_of_int => "static_cast<unsigned int>(%a0)".

Axiom nat_of_int_0 : nat_of_int 0 = 0%nat.
Axiom nat_of_int_pos : forall n, eqb n 0 = false -> exists m, nat_of_int n = S m.
Axiom nat_of_int_1 : nat_of_int 1 = 1%nat.
Axiom nat_of_int_gt1 : forall n, ltb 1 n = true -> exists m, nat_of_int n = S (S m).


From Corelib Require Import PrimString.
Axiom string_of_nat : nat -> string.
Crane Extract Inlined Constant string_of_nat => "std::to_string(%a0)".
