
val app : 'a1 list -> 'a1 list -> 'a1 list

val add : int -> int -> int

val sub : int -> int -> int

module Nat :
 sig
  val sub : int -> int -> int

  val eqb : int -> int -> bool

  val even : int -> bool

  val divmod : int -> int -> int -> int -> int * int

  val div : int -> int -> int

  val modulo : int -> int -> int

  val gcd : int -> int -> int

  val div2 : int -> int
 end

val remove_twos_aux : int -> int -> int

val remove_twos : int -> int

val remove_threes_aux : int -> int -> int

val remove_threes : int -> int

val is_2_3_smooth_b : int -> bool

val coprime : int -> int -> bool

val count_coprime : int -> int -> int

val euler_phi : int -> int

val count_smooth_aux : int -> int -> int

val list_smooth_aux : int -> int -> int list

val list_non_smooth_aux : int -> int -> int list

type constructLevel =
| Rational
| Compass
| Origami1
| Origami2
| Higher

val is_power_of_2_b : int -> bool

val classify_by_degree : int -> constructLevel

val ngon_constructible : int -> bool

val ngon_tool_required : int -> constructLevel

val list_constructible_in_range : int -> int -> int list

val list_non_constructible_in_range : int -> int -> int list

val count_constructible_in_range : int -> int -> int

val heptagon_cubic_p_num : int

val heptagon_cubic_p_den : int

val heptagon_cubic_q_num : int

val heptagon_cubic_q_den : int

val delian_cubic_p : int

val delian_cubic_q : int

val map_with_phi : int list -> (int * int) list

val classify_range_aux : int -> int -> ((int * int) * constructLevel) list

val classify_range : int -> int -> ((int * int) * constructLevel) list

val ngon_report : int -> ((int * int) * constructLevel) * bool

val batch_report_aux :
  int -> int -> (((int * int) * constructLevel) * bool) list

val batch_report : int -> int -> (((int * int) * constructLevel) * bool) list
