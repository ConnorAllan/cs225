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

type store = (loc * value) list
[@@deriving show {with_path = false}]

(* r ∈ result ⩴ v | ⟨e,s⟩ | stuck
 *)
type result =
  | Val of value
  | Step of exp * store
  | Stuck
[@@deriving show {with_path = false}]

(* Typing relation encoded as an inference metafunction. *)
let rec step (e0 : exp) : result = match e0 with
  (* true ∈ val *)
  | True -> Val(VTrue)
  (* false ∈ val *)
  | False -> Val(VFalse)
  | If(e1,e2,e3) -> begin match step e1 with
      (* [If-True]
       * if(true){e₂}{e₃} —→ e₂ *)
      | Val(VTrue) -> Step(e2)
      (* [If-False]
       * if(false){e₂}{e₃} —→ e₃ *)
      | Val(VFalse) -> Step(e3)
      (* v ∉ {true,false}
       * ⟹
       * if(v){e₂}{e₃} ∉ val
       * if(v){e₂}{e₃} —↛ *)
      | Val(_) -> Stuck
      (* [If-Cong]
       * e₁ —→ e₁′
       * ⟹
       * if(e₁){e₂}{e₃} —→ if(e₁′){e₂}{e₃} *)
      | Step(e1') -> Step(If(e1',e2,e3))
      (* e₁ ∉ val
       * e₁ —↛
       * ⟹
       * if(e₁){e₂}{e₃} ∉ val
       * if(e₁){e₂}{e₃} —↛ *)
      | Stuck -> Stuck
      end
  | Pair(e1,e2) -> begin match step e1 with
      | Val(v1) -> begin match step e2 with
          (* ⟨v₁,v₂⟩ ∈ val *)
          | Val(v2) -> Val(VPair(v1,v2))
          (* [Pair-Cong-2]
           * e —→ e′
           * ⟹
           * ⟨v,e⟩ —→ ⟨v,e′⟩ *)
          | Step(e2') -> Step(Pair(e1,e2'))
          (* e ∉ val
           * e —↛
           * ⟹
           * ⟨v,e⟩ ∉ val
           * ⟨v,e⟩ —↛ *)
          | Stuck -> Stuck
          end
      (* [Pair-Cong-1]
       * e₁ —→ e₁′
       * ⟹
       * ⟨e₁,e₂⟩ —→ ⟨e₁′,e₂⟩ *)
      | Step(e1') -> Step(Pair(e1',e2))
      (* e₁ ∉ val
       * e₁ —↛
       * ⟹
       * ⟨e₁,e₂⟩ ∉ val
       * ⟨e₁,e₂⟩ —↛ *)
      | Stuck -> Stuck
      end
  | Projl(e1) -> begin match step e1 with
      (* [Projl-Pair]
       * projl(⟨v₁,v₂⟩) —→ v₁ *)
      | Val(VPair(v1,v2)) -> Step(exp_of_val v1)
      (* ∄v₁,v₂. v = ⟨v₁,v₂⟩
       * ⟹
       * projl(v) ∉ val
       * projl(v) —↛ *)
      | Val(_) -> Stuck
      (* [Projl-Cong]
       * e —→ e′
       * ⟹
       * projl(e) —→ projl(e′) *)
      | Step(e1') -> Step(Projl(e1'))
      (* e ∉ val
       * e —↛
       * ⟹
       * projl(e) ∉ val
       * projl(e) —↛ *)
      | Stuck -> Stuck
      end
  | Projr(e1) -> begin match step e1 with
      (* [Projr-Pair]
       * projr(⟨v₁,v₂⟩) —→ v₂ *)
      | Val(VPair(v1,v2)) -> Step(exp_of_val v2)
      (* ∄v₁,v₂. v = ⟨v₁,v₂⟩
       * ⟹
       * projr(v) ∉ val
       * projr(v) —↛ *)
      | Val(_) -> Stuck
      (* [Projr-Cong]
       * e —→ e′
       * ⟹
       * projr(e) —→ projr(e′) *)
      | Step(e1') -> Step(Projr(e1'))
      (* e ∉ val
       * e —↛
       * ⟹
       * projr(e) ∉ val
       * projr(e) —↛ *)
      | Stuck -> Stuck
      end
      | Loc(l) -> Val(VLoc(l))
      | Try(e1,e2) ->
      | Raise(e) ->
