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

 (* ℓ ∈ loc ≈ ℕ
  *)
 type loc = int
 [@@deriving show {with_path = false}]

type exp =
  | True
  | False
  | If of exp * exp * exp
  | Pair of exp * exp
  | Projl of exp
  | Projr of exp
  | Loc of loc
  | Try of exp * exp
  | Raise of exp
[@@deriving show {with_path = false}]

(* Values.
 * v ∈ value ⩴ true | false
 *           | ⟨v,v⟩
 *           | loc(ℓ)
 *)
type value =
  | VTrue
  | VFalse
  | VPair of value * value
  | VLoc of loc
[@@deriving show {with_path = false}]

let rec exp_of_val (v : value) : exp = match v with
  | VTrue -> True
  | VFalse -> False
  | VPair(v1,v2) -> Pair(exp_of_val v1,exp_of_val v2)
  | VLoc(l) -> Loc(l)

type store = (loc * value) list
[@@deriving show {with_path = false}]

(* r ∈ result ⩴ v | ⟨e,s⟩ | stuck
 *)
type result =
  | Val of value
  | Step of exp * store
  | Stuck
[@@deriving show {with_path = false}]

let rec step (e0 : exp) (s : store) : result = match e0 with
  | True -> Val(VTrue)
  | False -> Val(VFalse)
  | If(e1,e2,e3) -> begin match step e1 s with
      | Val(VTrue) -> Step(e2,s)
      | Val(VFalse) -> Step(e3,s)
      | Val(_) -> Stuck
      | Step(e1',s') -> Step(If(e1',e2,e3),s')
      | Stuck -> Stuck
      end
  | Pair(e1,e2) -> begin match step e1 s with
      | Val(v1) -> begin match step e2 s with
          | Val(v2) -> Val(VPair(v1,v2))
          | Step(e2',s') -> Step(Pair(e1,e2'),s')
          | Stuck -> Stuck
          end
      | Step(e1',s') -> Step(Pair(e1',e2),s')
      | Stuck -> Stuck
      end
  | Projl(e1) -> begin match step e1 s with
      | Val(VPair(v1,v2)) -> Step(exp_of_val v1,s)
      | Val(_) -> Stuck                                                      
      | Step(e1',s') -> Step(Projl(e1'),s')
      | Stuck -> Stuck
      end
  | Projr(e1) -> begin match step e1 s with
      | Val(VPair(v1,v2)) -> Step(exp_of_val v2,s)
      | Val(_) -> Stuck
      | Step(e1',s') -> Step(Projr(e1'),s')
      | Stuck -> Stuck
      end
      | Loc(l) -> Val(VLoc(l))
      | Try(e1,e2) ->
      | Raise(e) ->
