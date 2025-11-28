
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

(** val count_smooth_aux : int -> int -> int **)

let rec count_smooth_aux fuel lo =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> 0)
    (fun f ->
    add (if is_2_3_smooth_b (euler_phi lo) then succ 0 else 0)
      (count_smooth_aux f (succ lo)))
    fuel

(** val list_smooth_aux : int -> int -> int list **)

let rec list_smooth_aux fuel lo =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> [])
    (fun f ->
    app (if is_2_3_smooth_b (euler_phi lo) then lo::[] else [])
      (list_smooth_aux f (succ lo)))
    fuel

(** val list_non_smooth_aux : int -> int -> int list **)

let rec list_non_smooth_aux fuel lo =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> [])
    (fun f ->
    app (if is_2_3_smooth_b (euler_phi lo) then [] else lo::[])
      (list_non_smooth_aux f (succ lo)))
    fuel

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
