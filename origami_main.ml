(** origami_main.ml — Entry point for certified library with float geometry *)

open Origami_lib

let tool_to_string = function
  | Rational -> "RATIONAL"
  | Compass  -> "COMPASS"
  | Origami1 -> "ORIGAMI-1"
  | Origami2 -> "ORIGAMI-2"
  | Higher   -> "HIGHER"

let print_report ((((n, phi), tool), constr) : ((int * int) * constructLevel) * bool) =
  Printf.printf "  %3d  |  %4d  |  %-9s  |  %s\n"
    n phi (tool_to_string tool) (if constr then "YES" else "NO")

let () =
  print_endline "════════════════════════════════════════════════════════════════";
  print_endline "  ORIGAMI CONSTRUCTIBILITY — Coq-Verified with Float Geometry";
  print_endline "════════════════════════════════════════════════════════════════";
  print_newline ();

  print_endline "N-GON CONSTRUCTIBILITY TABLE:";
  print_endline "┌───────┬────────┬─────────────┬──────────────┐";
  print_endline "│   n   │  φ(n)  │    Tool     │ Constructible│";
  print_endline "├───────┼────────┼─────────────┼──────────────┤";
  List.iter print_report (batch_report 3 21);
  print_endline "└───────┴────────┴─────────────┴──────────────┘";
  print_newline ();

  print_endline "FLOAT GEOMETRY (Extracted from Coq):";
  Printf.printf "  Pi constant:     %.15f\n" FloatGeom.float_pi;
  Printf.printf "  Heptagon p:      %.15f\n" FloatGeom.float_heptagon_p;
  Printf.printf "  Heptagon q:      %.15f\n" FloatGeom.float_heptagon_q;
  Printf.printf "  Delian p:        %.15f\n" FloatGeom.float_delian_p;
  Printf.printf "  Delian q:        %.15f\n" FloatGeom.float_delian_q;
  print_newline ();

  print_endline "CUBIC DISCRIMINANT TEST:";
  let hp, hq = FloatGeom.float_heptagon_p, FloatGeom.float_heptagon_q in
  Printf.printf "  Heptagon cubic:  t³ + (%.6f)t + (%.6f) = 0\n" hp hq;
  Printf.printf "  Discriminant:    %.10f\n" (FloatGeom.float_cubic_discriminant hp hq);
  print_newline ();

  print_endline "POINT REFLECTION TEST:";
  let p1 = (1.0, 0.0) in
  let line_y = ((0.0, 1.0), 0.0) in  (* y-axis: x = 0 *)
  let p2 = FloatGeom.float_reflect p1 line_y in
  Printf.printf "  Point (1, 0) reflected across y-axis: (%.1f, %.1f)\n" (fst p2) (snd p2);
  print_newline ();

  print_endline "N-GON CENTRAL ANGLES:";
  for n = 5 to 12 do
    Printf.printf "  %2d-gon: 2π/%d = %.10f rad\n" n n (FloatGeom.float_ngon_angle n)
  done;
  print_newline ();

  print_endline "SINGLE-FOLD CONSTRUCTIBLE (3-50):";
  print_string "  ";
  List.iter (Printf.printf "%d ") (list_constructible_in_range 3 51);
  print_newline ();
  print_newline ();

  print_endline "REQUIRES 2-FOLD (3-50):";
  print_string "  ";
  List.iter (Printf.printf "%d ") (list_non_constructible_in_range 3 51);
  print_newline ();
  print_newline ();

  Printf.printf "STATISTICS (n=3 to 100): %d constructible, %d require 2-fold\n"
    (count_constructible_in_range 3 101)
    (98 - count_constructible_in_range 3 101);
  print_endline "════════════════════════════════════════════════════════════════"
