(** origami.ml — IO layer for certified kernel
    Build: cat origami_kernel.ml origami.ml > origami_run.ml
    Run:   ocaml origami_run.ml *)

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
  print_endline "  ORIGAMI CONSTRUCTIBILITY — Coq-Verified Kernel";
  print_endline "  Source: origami.v (13,742 lines, fully machine-checked)";
  print_endline "════════════════════════════════════════════════════════════════";
  print_newline ();

  print_endline "┌───────┬────────┬─────────────┬──────────────┐";
  print_endline "│   n   │  φ(n)  │    Tool     │ Constructible│";
  print_endline "├───────┼────────┼─────────────┼──────────────┤";
  List.iter print_report (batch_report 3 21);
  print_endline "└───────┴────────┴─────────────┴──────────────┘";
  print_newline ();

  print_endline "KEY RESULTS:";
  Printf.printf "  Heptagon (7-gon):    φ(7)=%d   → %s\n"
    (euler_phi 7) (tool_to_string (ngon_tool_required 7));
  Printf.printf "  Hendecagon (11-gon): φ(11)=%d  → %s (boundary case)\n"
    (euler_phi 11) (tool_to_string (ngon_tool_required 11));
  print_newline ();

  print_endline "O6 BELOCH FOLD PARAMETERS:";
  Printf.printf "  Heptagon:  t³ + (%d/%d)t + (%d/%d) = 0\n"
    heptagon_cubic_p_num heptagon_cubic_p_den
    heptagon_cubic_q_num heptagon_cubic_q_den;
  Printf.printf "  Delian:    t³ + %dt + %d = 0  (cube doubling)\n"
    delian_cubic_p delian_cubic_q;
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
