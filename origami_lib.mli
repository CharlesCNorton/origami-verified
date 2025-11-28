module Uint63 : sig
  type t = int
  val of_int : int -> t
end

module Float64 : sig
  type t = float
  val of_float : float -> t
end


val fst : ('a1 * 'a2) -> 'a1

val snd : ('a1 * 'a2) -> 'a2

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

module Pos :
 sig
  val succ : int -> int

  val of_succ_nat : int -> int
 end

module Z :
 sig
  val of_nat : int -> int
 end

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

val seq : int -> int -> int list

(* type int - using OCaml native int *)

val lsl0 : int -> int -> int

val lor0 : int -> int -> int

val sub0 : int -> int -> int

val opp : Float64.t -> Float64.t

val eqb0 : Float64.t -> Float64.t -> bool

val mul : Float64.t -> Float64.t -> Float64.t

val add0 : Float64.t -> Float64.t -> Float64.t

val sub1 : Float64.t -> Float64.t -> Float64.t

val div0 : Float64.t -> Float64.t -> Float64.t

val of_uint63 : int -> Float64.t

val size : int

val opp0 : int -> int

val of_pos_rec : int -> int -> int

val of_pos : int -> int

val of_Z : int -> int

val remove_twos_aux : int -> int -> int

val remove_twos : int -> int

val remove_threes_aux : int -> int -> int

val remove_threes : int -> int

val is_2_3_smooth_b : int -> bool

val coprime : int -> int -> bool

val count_coprime : int -> int -> int

val euler_phi : int -> int

val crt_pair : int -> int -> int -> int * int

val minpoly_2cos_degree : int

val algebraic_degree_cos_2pi_11 : int

val count_smooth_aux : int -> int -> int

val count_smooth_in_range : int -> int -> int

val density_numerator : int -> int -> int

val density_denominator : int -> int -> int

val list_smooth_aux : int -> int -> int list

val list_smooth_in_range : int -> int -> int list

val list_non_smooth_aux : int -> int -> int list

val list_non_smooth_in_range : int -> int -> int list

val constructible_3_to_50 : int

val constructible_3_to_100 : int

val first_non_constructible : int list

type constructLevel =
| Rational
| Compass
| Origami1
| Origami2
| Higher

val is_power_of_2_b : int -> bool

val classify_by_degree : int -> constructLevel

val sqrt2_degree : int

val cbrt2_degree : int

val cos_2pi_7_degree : int

val cos_2pi_11_degree : int

val cos_2pi_17_degree : int

val classification_summary : (int * constructLevel) list

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

module FloatGeom :
 sig
  val float_pi : Float64.t

  type float_point = Float64.t * Float64.t

  type float_line = (Float64.t * Float64.t) * Float64.t

  val fpx : float_point -> Float64.t

  val fpy : float_point -> Float64.t

  val fla : float_line -> Float64.t

  val flb : float_line -> Float64.t

  val flc : float_line -> Float64.t

  val float_dist2 : float_point -> float_point -> Float64.t

  val float_midpoint : float_point -> float_point -> float_point

  val float_line_through : float_point -> float_point -> float_line

  val float_reflect : float_point -> float_line -> float_point

  val float_perp_bisector : float_point -> float_point -> float_line

  val float_line_intersection : float_line -> float_line -> float_point option

  val float_fold_O1 : float_point -> float_point -> float_line

  val float_fold_O2 : float_point -> float_point -> float_line

  val float_beloch_crease : Float64.t -> float_line

  val float_depressed_cubic : Float64.t -> Float64.t -> Float64.t -> Float64.t

  val float_cubic_discriminant : Float64.t -> Float64.t -> Float64.t

  val float_cardano_discriminant : Float64.t -> Float64.t -> Float64.t

  val float_heptagon_p : Float64.t

  val float_heptagon_q : Float64.t

  val float_delian_p : Float64.t

  val float_delian_q : Float64.t

  val float_ngon_angle : int -> Float64.t
 end
