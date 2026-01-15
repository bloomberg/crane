
val negb : bool -> bool

val fst : ('a1 * 'a2) -> 'a1

val snd : ('a1 * 'a2) -> 'a2

val length : 'a1 list -> int

val eqb : int -> int -> bool

type string =
  String.t;;
module Pstring = struct
  let unsafe_of_string = fun s -> s
end;;

val cat : string -> string -> string

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1

val filter : ('a1 -> bool) -> 'a1 list -> 'a1 list

val find : ('a1 -> bool) -> 'a1 list -> 'a1 option

val one : int

val two : int

val three : int

val four : int

val five : int

val six : int

val seven : int

val eight : int

val nine : int

val ten : int

val eleven : int

val twelve : int

val thirteen : int

val fourteen : int

val fifteen : int

val sixteen : int

val seventeen : int

val eighteen : int

val nineteen : int

val twenty : int

val twenty_one : int

val twenty_two : int

val twenty_three : int

val twenty_four : int

val twenty_five : int

val twenty_six : int

val twenty_seven : int

val twenty_eight : int

val twenty_nine : int

val thirty : int

val thirty_one : int

val thirty_two : int

val thirty_three : int

val thirty_four : int

val thirty_five : int

val thirty_six : int

val thirty_seven : int

val thirty_eight : int

val thirty_nine : int

val forty : int

val forty_one : int

val forty_two : int

val forty_three : int

val forty_four : int

val forty_five : int

val forty_six : int

val forty_seven : int

val forty_eight : int

val forty_nine : int

val fifty : int

val fifty_one : int

val fifty_two : int

val fifty_three : int

val fifty_four : int

val fifty_five : int

val fifty_six : int

val fifty_seven : int

val fifty_eight : int

val fifty_nine : int

val sixty : int

val sixty_one : int

val sixty_two : int

val sixty_three : int

val sixty_four : int

val sixty_five : int

val sixty_six : int

val sixty_seven : int

val sixty_eight : int

val sixty_nine : int

val seventy : int

val seventy_one : int

val seventy_two : int

val seventy_three : int

val seventy_four : int

val seventy_five : int

val seventy_six : int

val seventy_seven : int

val seventy_eight : int

val seventy_nine : int

val eighty : int

val eighty_one : int

val eighty_two : int

val eighty_three : int

val eighty_four : int

val eighty_five : int

val eighty_six : int

val eighty_seven : int

val eighty_eight : int

val eighty_nine : int

val ninety : int

val ninety_one : int

val ninety_two : int

val ninety_three : int

val ninety_four : int

val ninety_five : int

val ninety_six : int

val ninety_seven : int

val ninety_eight : int

val ninety_nine : int

val one_hundred : int

val one_hundred_one : int

val one_hundred_two : int

val one_hundred_three : int

val one_hundred_four : int

val one_hundred_five : int

val one_hundred_six : int

val one_hundred_seven : int

val one_hundred_eight : int

val one_hundred_nine : int

val one_hundred_ten : int

val one_hundred_eleven : int

val one_hundred_twelve : int

val one_hundred_thirteen : int

val one_hundred_fourteen : int

val one_hundred_fifteen : int

val one_hundred_sixteen : int

val one_hundred_seventeen : int

val one_hundred_eighteen : int

val one_hundred_nineteen : int

val one_hundred_twenty : int

val one_hundred_twenty_one : int

val one_hundred_twenty_two : int

val one_hundred_twenty_three : int

val one_hundred_twenty_four : int

val one_hundred_twenty_five : int

val one_hundred_twenty_six : int

val one_hundred_twenty_seven : int

val one_hundred_twenty_eight : int

val one_hundred_twenty_nine : int

val one_hundred_thirty : int

val one_hundred_thirty_one : int

val one_hundred_thirty_two : int

val one_hundred_thirty_three : int

val one_hundred_thirty_four : int

val one_hundred_thirty_five : int

val one_hundred_thirty_six : int

val one_hundred_thirty_seven : int

val one_hundred_thirty_eight : int

val one_hundred_thirty_nine : int

val one_hundred_forty : int

val one_hundred_forty_one : int

val one_hundred_forty_two : int

val one_hundred_forty_three : int

val one_hundred_forty_four : int

val one_hundred_forty_five : int

val one_hundred_forty_six : int

val one_hundred_forty_seven : int

val one_hundred_forty_eight : int

val one_hundred_forty_nine : int

val one_hundred_fifty : int



module ToString :
 sig
  val intersperse : ('a1 -> string) -> string -> 'a1 list -> string

  val list_to_string : ('a1 -> string) -> 'a1 list -> string
 end

module TopSort :
 sig
  type 'node entry = 'node * 'node list

  type 'node graph = 'node entry list

  type 'node order = 'node list list

  val graph_lookup : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 graph -> 'a1 list

  val contains : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 list -> bool

  val cycle_entry_aux :
    ('a1 -> 'a1 -> bool) -> 'a1 graph -> 'a1 list -> 'a1 -> int -> 'a1

  val cycle_entry : ('a1 -> 'a1 -> bool) -> 'a1 graph -> 'a1 option

  val cycle_extract_aux :
    ('a1 -> 'a1 -> bool) -> 'a1 graph -> int -> 'a1 -> 'a1 list -> 'a1 list

  val cycle_extract : ('a1 -> 'a1 -> bool) -> 'a1 graph -> 'a1 list

  val null : 'a1 list -> bool

  val topological_sort_aux :
    ('a1 -> 'a1 -> bool) -> 'a1 graph -> int -> 'a1 order

  val topological_sort_graph : ('a1 -> 'a1 -> bool) -> 'a1 graph -> 'a1 order
 end

val bigDAG : (int * int list) list

val benchmark : unit -> string
