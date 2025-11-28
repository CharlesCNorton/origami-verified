module Uint63 = struct
  type t = int
  let of_int x = x
end

module Float64 = struct
  type t = float
  let of_float x = x
end


(** val fst : ('a1 * 'a2) -> 'a1 **)

let fst = function
| x,_ -> x

(** val snd : ('a1 * 'a2) -> 'a2 **)

let snd = function
| _,y -> y

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | [] -> m
  | a::l1 -> a::(app l1 m)

(** val add : int -> int -> int **)

let rec add = (+)

(** val sub : int -> int -> int **)

let rec sub = (fun n m -> max 0 (n-m))

module Nat =
 struct
  (** val sub : int -> int -> int **)

  let rec sub n m =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> n)
      (fun k ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> n)
        (fun l -> sub k l)
        m)
      n

  (** val eqb : int -> int -> bool **)

  let rec eqb = (=)

  (** val even : int -> bool **)

  let rec even n =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> true)
      (fun n0 ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> false)
        (fun n' -> even n')
        n0)
      n

  (** val divmod : int -> int -> int -> int -> int * int **)

  let rec divmod x y q u =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> q,u)
      (fun x' ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> divmod x' y (succ q) y)
        (fun u' -> divmod x' y q u')
        u)
      x

  (** val div : int -> int -> int **)

  let div = (/)

  (** val modulo : int -> int -> int **)

  let modulo = (mod)

  (** val gcd : int -> int -> int **)

  let rec gcd a b =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> b)
      (fun a' -> gcd (modulo b (succ a')) (succ a'))
      a

  (** val div2 : int -> int **)

  let rec div2 = fun n -> n/2
 end

module Pos =
 struct
  (** val succ : int -> int **)

  let rec succ = Stdlib.Int.succ

  (** val of_succ_nat : int -> int **)

  let rec of_succ_nat n =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> 1)
      (fun x -> succ (of_succ_nat x))
      n
 end

module Z =
 struct
  (** val of_nat : int -> int **)

  let of_nat n =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> 0)
      (fun n0 -> (Pos.of_succ_nat n0))
      n
 end

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| [] -> []
| a::t -> (f a)::(map f t)

(** val seq : int -> int -> int list **)

let rec seq start len =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> [])
    (fun len0 -> start::(seq (succ start) len0))
    len

(* type int - using OCaml native int *)

(** val lsl0 : int -> int -> int **)

let lsl0 = (lsl)

(** val lor0 : int -> int -> int **)

let lor0 = (lor)

(** val sub0 : int -> int -> int **)

let sub0 = (-)

(** val opp : Float64.t -> Float64.t **)

let opp = (~-.)

(** val eqb0 : Float64.t -> Float64.t -> bool **)

let eqb0 = (=)

(** val mul : Float64.t -> Float64.t -> Float64.t **)

let mul = ( *.)

(** val add0 : Float64.t -> Float64.t -> Float64.t **)

let add0 = (+.)

(** val sub1 : Float64.t -> Float64.t -> Float64.t **)

let sub1 = (-.)

(** val div0 : Float64.t -> Float64.t -> Float64.t **)

let div0 = (/.)

(** val of_uint63 : int -> Float64.t **)

let of_uint63 = Float.of_int

(** val size : int **)

let size =
  succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ
    0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val opp0 : int -> int **)

let opp0 i =
  sub0 (Uint63.of_int (0)) i

(** val of_pos_rec : int -> int -> int **)

let rec of_pos_rec n p =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> (Uint63.of_int (0)))
    (fun n0 ->
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 ->
      lor0 (lsl0 (of_pos_rec n0 p0) (Uint63.of_int (1))) (Uint63.of_int (1)))
      (fun p0 -> lsl0 (of_pos_rec n0 p0) (Uint63.of_int (1)))
      (fun _ -> (Uint63.of_int (1)))
      p)
    n

(** val of_pos : int -> int **)

let of_pos =
  of_pos_rec size

(** val of_Z : int -> int **)

let of_Z z0 =
  (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
    (fun _ -> (Uint63.of_int (0)))
    (fun p -> of_pos p)
    (fun p -> opp0 (of_pos p))
    z0

(** val remove_twos_aux : int -> int -> int **)

let rec remove_twos_aux n fuel =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> n)
    (fun fuel' ->
    if Nat.even n then remove_twos_aux (Nat.div2 n) fuel' else n)
    fuel

(** val remove_twos : int -> int **)

let remove_twos n =
  remove_twos_aux n n

(** val remove_threes_aux : int -> int -> int **)

let rec remove_threes_aux n fuel =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> n)
    (fun fuel' ->
    if Nat.eqb (Nat.modulo n (succ (succ (succ 0)))) 0
    then remove_threes_aux (Nat.div n (succ (succ (succ 0)))) fuel'
    else n)
    fuel

(** val remove_threes : int -> int **)

let remove_threes n =
  remove_threes_aux n n

(** val is_2_3_smooth_b : int -> bool **)

let is_2_3_smooth_b n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> false)
    (fun _ -> Nat.eqb (remove_threes (remove_twos n)) (succ 0))
    n

(** val coprime : int -> int -> bool **)

let coprime a b =
  Nat.eqb (Nat.gcd a b) (succ 0)

(** val count_coprime : int -> int -> int **)

let rec count_coprime n k =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> 0)
    (fun k' ->
    add (if coprime (succ k') n then succ 0 else 0) (count_coprime n k'))
    k

(** val euler_phi : int -> int **)

let euler_phi n =
  count_coprime n n

(** val crt_pair : int -> int -> int -> int * int **)

let crt_pair m n k =
  (Nat.modulo k m),(Nat.modulo k n)

(** val minpoly_2cos_degree : int **)

let minpoly_2cos_degree =
  succ (succ (succ (succ (succ 0))))

(** val algebraic_degree_cos_2pi_11 : int **)

let algebraic_degree_cos_2pi_11 =
  succ (succ (succ (succ (succ 0))))

(** val count_smooth_aux : int -> int -> int **)

let rec count_smooth_aux fuel lo =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> 0)
    (fun f ->
    add (if is_2_3_smooth_b (euler_phi lo) then succ 0 else 0)
      (count_smooth_aux f (succ lo)))
    fuel

(** val count_smooth_in_range : int -> int -> int **)

let count_smooth_in_range lo hi =
  count_smooth_aux (sub hi lo) lo

(** val density_numerator : int -> int -> int **)

let density_numerator =
  count_smooth_in_range

(** val density_denominator : int -> int -> int **)

let density_denominator lo hi =
  sub hi lo

(** val list_smooth_aux : int -> int -> int list **)

let rec list_smooth_aux fuel lo =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> [])
    (fun f ->
    app (if is_2_3_smooth_b (euler_phi lo) then lo::[] else [])
      (list_smooth_aux f (succ lo)))
    fuel

(** val list_smooth_in_range : int -> int -> int list **)

let list_smooth_in_range lo hi =
  list_smooth_aux (sub hi lo) lo

(** val list_non_smooth_aux : int -> int -> int list **)

let rec list_non_smooth_aux fuel lo =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> [])
    (fun f ->
    app (if is_2_3_smooth_b (euler_phi lo) then [] else lo::[])
      (list_non_smooth_aux f (succ lo)))
    fuel

(** val list_non_smooth_in_range : int -> int -> int list **)

let list_non_smooth_in_range lo hi =
  list_non_smooth_aux (sub hi lo) lo

(** val constructible_3_to_50 : int **)

let constructible_3_to_50 =
  count_smooth_in_range (succ (succ (succ 0))) (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    0)))))))))))))))))))))))))))))))))))))))))))))))))))

(** val constructible_3_to_100 : int **)

let constructible_3_to_100 =
  count_smooth_in_range (succ (succ (succ 0))) (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val first_non_constructible : int list **)

let first_non_constructible =
  list_non_smooth_in_range (succ (succ (succ 0))) (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ
    0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

type constructLevel =
| Rational
| Compass
| Origami1
| Origami2
| Higher

(** val is_power_of_2_b : int -> bool **)

let is_power_of_2_b n =
  Nat.eqb (remove_twos n) (succ 0)

(** val classify_by_degree : int -> constructLevel **)

let classify_by_degree d =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> Rational)
    (fun n ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> Rational)
      (fun _ ->
      if is_power_of_2_b d
      then Compass
      else if is_2_3_smooth_b d then Origami1 else Higher)
      n)
    d

(** val sqrt2_degree : int **)

let sqrt2_degree =
  succ (succ 0)

(** val cbrt2_degree : int **)

let cbrt2_degree =
  succ (succ (succ 0))

(** val cos_2pi_7_degree : int **)

let cos_2pi_7_degree =
  succ (succ (succ 0))

(** val cos_2pi_11_degree : int **)

let cos_2pi_11_degree =
  succ (succ (succ (succ (succ 0))))

(** val cos_2pi_17_degree : int **)

let cos_2pi_17_degree =
  succ (succ (succ (succ (succ (succ (succ (succ 0)))))))

(** val classification_summary : (int * constructLevel) list **)

let classification_summary =
  map (fun d -> d,(classify_by_degree d))
    (seq (succ 0) (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
      (succ (succ (succ (succ (succ 0))))))))))))))))

(** val ngon_constructible : int -> bool **)

let ngon_constructible n =
  is_2_3_smooth_b (euler_phi n)

(** val ngon_tool_required : int -> constructLevel **)

let ngon_tool_required n =
  let phi = euler_phi n in
  if is_power_of_2_b phi
  then Compass
  else if is_2_3_smooth_b phi then Origami1 else Origami2

(** val list_constructible_in_range : int -> int -> int list **)

let list_constructible_in_range lo hi =
  list_smooth_aux (sub hi lo) lo

(** val list_non_constructible_in_range : int -> int -> int list **)

let list_non_constructible_in_range lo hi =
  list_non_smooth_aux (sub hi lo) lo

(** val count_constructible_in_range : int -> int -> int **)

let count_constructible_in_range lo hi =
  count_smooth_aux (sub hi lo) lo

(** val heptagon_cubic_p_num : int **)

let heptagon_cubic_p_num =
  (~-) ((fun p->1+2*p) ((fun p->1+2*p) 1))

(** val heptagon_cubic_p_den : int **)

let heptagon_cubic_p_den =
  ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) 1)))

(** val heptagon_cubic_q_num : int **)

let heptagon_cubic_q_num =
  (~-) ((fun p->1+2*p) ((fun p->1+2*p) 1))

(** val heptagon_cubic_q_den : int **)

let heptagon_cubic_q_den =
  ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p)
    ((fun p->2*p) ((fun p->1+2*p) 1)))))))

(** val delian_cubic_p : int **)

let delian_cubic_p =
  0

(** val delian_cubic_q : int **)

let delian_cubic_q =
  (~-) ((fun p->2*p) 1)

(** val map_with_phi : int list -> (int * int) list **)

let rec map_with_phi = function
| [] -> []
| n::rest -> (n,(euler_phi n))::(map_with_phi rest)

(** val classify_range_aux :
    int -> int -> ((int * int) * constructLevel) list **)

let rec classify_range_aux fuel lo =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> [])
    (fun f ->
    ((lo,(euler_phi lo)),(ngon_tool_required lo))::(classify_range_aux f
                                                     (succ lo)))
    fuel

(** val classify_range : int -> int -> ((int * int) * constructLevel) list **)

let classify_range lo hi =
  classify_range_aux (sub hi lo) lo

(** val ngon_report : int -> ((int * int) * constructLevel) * bool **)

let ngon_report n =
  ((n,(euler_phi n)),(ngon_tool_required n)),(ngon_constructible n)

(** val batch_report_aux :
    int -> int -> (((int * int) * constructLevel) * bool) list **)

let rec batch_report_aux fuel lo =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> [])
    (fun f -> (ngon_report lo)::(batch_report_aux f (succ lo)))
    fuel

(** val batch_report :
    int -> int -> (((int * int) * constructLevel) * bool) list **)

let batch_report lo hi =
  batch_report_aux (sub hi lo) lo

module FloatGeom =
 struct
  (** val float_pi : Float64.t **)

  let float_pi =
    (Float64.of_float (0x1.921fb54442d18p+1))

  type float_point = Float64.t * Float64.t

  type float_line = (Float64.t * Float64.t) * Float64.t

  (** val fpx : float_point -> Float64.t **)

  let fpx =
    fst

  (** val fpy : float_point -> Float64.t **)

  let fpy =
    snd

  (** val fla : float_line -> Float64.t **)

  let fla l =
    fst (fst l)

  (** val flb : float_line -> Float64.t **)

  let flb l =
    snd (fst l)

  (** val flc : float_line -> Float64.t **)

  let flc =
    snd

  (** val float_dist2 : float_point -> float_point -> Float64.t **)

  let float_dist2 p1 p2 =
    let dx = sub1 (fpx p1) (fpx p2) in
    let dy = sub1 (fpy p1) (fpy p2) in add0 (mul dx dx) (mul dy dy)

  (** val float_midpoint : float_point -> float_point -> float_point **)

  let float_midpoint p1 p2 =
    (div0 (add0 (fpx p1) (fpx p2)) (Float64.of_float (0x1p+1))),(div0
                                                                  (add0
                                                                    (fpy p1)
                                                                    (fpy p2))
                                                                  (Float64.of_float (0x1p+1)))

  (** val float_line_through : float_point -> float_point -> float_line **)

  let float_line_through p1 p2 =
    let x1 = fpx p1 in
    let y1 = fpy p1 in
    let x2 = fpx p2 in
    let y2 = fpy p2 in
    let a = sub1 y2 y1 in
    let b = sub1 x1 x2 in let c = opp (add0 (mul a x1) (mul b y1)) in (a,b),c

  (** val float_reflect : float_point -> float_line -> float_point **)

  let float_reflect p l =
    let x = fpx p in
    let y = fpy p in
    let a = fla l in
    let b = flb l in
    let c = flc l in
    let norm2 = add0 (mul a a) (mul b b) in
    let k =
      div0
        (mul (Float64.of_float (0x1p+1)) (add0 (add0 (mul a x) (mul b y)) c))
        norm2
    in
    (sub1 x (mul k a)),(sub1 y (mul k b))

  (** val float_perp_bisector : float_point -> float_point -> float_line **)

  let float_perp_bisector p1 p2 =
    let mx = fst (float_midpoint p1 p2) in
    let my = snd (float_midpoint p1 p2) in
    let dx = sub1 (fpx p2) (fpx p1) in
    let dy = sub1 (fpy p2) (fpy p1) in
    (dx,dy),(opp (add0 (mul dx mx) (mul dy my)))

  (** val float_line_intersection :
      float_line -> float_line -> float_point option **)

  let float_line_intersection l1 l2 =
    let a1 = fla l1 in
    let b1 = flb l1 in
    let c1 = flc l1 in
    let a2 = fla l2 in
    let b2 = flb l2 in
    let c2 = flc l2 in
    let det = sub1 (mul a1 b2) (mul a2 b1) in
    if eqb0 det (Float64.of_float (0x0p+0))
    then None
    else Some
           ((div0 (sub1 (mul b1 c2) (mul b2 c1)) det),(div0
                                                        (sub1 (mul a2 c1)
                                                          (mul a1 c2)) det))

  (** val float_fold_O1 : float_point -> float_point -> float_line **)

  let float_fold_O1 =
    float_line_through

  (** val float_fold_O2 : float_point -> float_point -> float_line **)

  let float_fold_O2 =
    float_perp_bisector

  (** val float_beloch_crease : Float64.t -> float_line **)

  let float_beloch_crease t =
    (t,(Float64.of_float (-0x1p+0))),(opp (mul t t))

  (** val float_depressed_cubic :
      Float64.t -> Float64.t -> Float64.t -> Float64.t **)

  let float_depressed_cubic p q t =
    add0 (add0 (mul (mul t t) t) (mul p t)) q

  (** val float_cubic_discriminant : Float64.t -> Float64.t -> Float64.t **)

  let float_cubic_discriminant p q =
    sub1 (mul (mul (mul (Float64.of_float (-0x1p+2)) p) p) p)
      (mul (mul (Float64.of_float (0x1.bp+4)) q) q)

  (** val float_cardano_discriminant : Float64.t -> Float64.t -> Float64.t **)

  let float_cardano_discriminant p q =
    add0 (div0 (mul q q) (Float64.of_float (0x1p+2)))
      (div0 (mul (mul p p) p) (Float64.of_float (0x1.bp+4)))

  (** val float_heptagon_p : Float64.t **)

  let float_heptagon_p =
    div0 (Float64.of_float (-0x1.cp+2)) (Float64.of_float (0x1.8p+3))

  (** val float_heptagon_q : Float64.t **)

  let float_heptagon_q =
    div0 (Float64.of_float (-0x1.cp+2)) (Float64.of_float (0x1.bp+7))

  (** val float_delian_p : Float64.t **)

  let float_delian_p =
    (Float64.of_float (0x0p+0))

  (** val float_delian_q : Float64.t **)

  let float_delian_q =
    (Float64.of_float (-0x1p+1))

  (** val float_ngon_angle : int -> Float64.t **)

  let float_ngon_angle n =
    div0 (mul (Float64.of_float (0x1p+1)) float_pi)
      (of_uint63 (of_Z (Z.of_nat n)))
 end
