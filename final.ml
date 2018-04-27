(* Name: Connor Allan *)
(* Name: Aaron Longchamp *)
(* Course: UVM CS 225 Spring 2018 - Darais *)
(* Final Project *)

open Util
open StringSetMap

(* Types.
 *
 * τ ∈ ty ⩴ bool
 *        | val
 *        | error
 *)
type ty =
  | Bool
  | Val
  | Error
[@@deriving show {with_path = false}]

(* Expressions.
 *
 * e ∈ exp ⩴ true | false | if(e){e}{e}
 *         | ⟨e,e⟩ | projl(e) | projr(e)
 *         | try (e) with (e) | raise(e)
 *)

type exp =
  | True
  | False
  | If of exp * exp * exp
  | Pair of exp * exp
  | Projl of exp
  | Projr of exp
  | Try of exp * exp
  | Raise of exp
[@@deriving show {with_path = false}]
