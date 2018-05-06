(* Name: Connor Allan *)
(* Name: Aaron Longchamp *)
(* Course: UVM CS 225 Spring 2018 - Darais *)
(* Final Project *)
(*
open Util
open StringSetMap
*)

exception NOT_FOUND

(* Types.
 *
 * τ ∈ ty ⩴ bool
 *        | val
 *        | prod(ty,ty)
 *)
type ty =
  | Bool
  | Val
  | Prod of ty * ty
[@@deriving show {with_path = false}]

(* Expressions.
 *
 * e ∈ exp ⩴ true | false | if(e){e}{e}
 *         | ⟨e,e⟩ | projl(e) | projr(e)
 *         | try (e) with (e) | raise(e)
 *         | error
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
 *           | error
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
  | Error
[@@deriving show {with_path = false}]

(*  Step functions*)
let rec step (e0 : exp) (s : store) : result = match e0 with
  | True -> Val(VTrue)
  | False -> Val(VFalse)
  | If(e1,e2,e3) -> begin match step e1 s with
      | Val(VTrue) -> Step(e2,s)
      | Val(VFalse) -> Step(e3,s)
      | Val(_) -> Stuck
      | Step(e1',s') -> Step(If(e1',e2,e3),s')
      | Error -> Error
      | Stuck -> Stuck
      end
  | Pair(e1,e2) -> begin match step e1 s with
      | Val(v1) -> begin match step e2 s with
          | Val(v2) -> Val(VPair(v1,v2))
          | Step(e2',s') -> Step(Pair(e1,e2'),s')
          | Error -> Error
          | Stuck -> Stuck
          end
      | Step(e1',s') -> Step(Pair(e1',e2),s')
      | Error -> Error
      | Stuck -> Stuck
      end
  | Projl(e1) -> begin match step e1 s with
      | Val(VPair(v1,v2)) -> Step(exp_of_val v1,s)
      | Val(_) -> Stuck
      | Step(e1',s') -> Step(Projl(e1'),s')
      | Error -> Error
      | Stuck -> Stuck
      end
  | Projr(e1) -> begin match step e1 s with
      | Val(VPair(v1,v2)) -> Step(exp_of_val v2,s)
      | Val(_) -> Stuck
      | Step(e1',s') -> Step(Projr(e1'),s')
      | Error -> Error
      | Stuck -> Stuck
      end
  | Loc(l) -> Val(VLoc(l))
  | Raise(e1) -> begin match step e1 s with
      | Val(v1) -> Step(exp_of_val v1, s)
      | Step(e1',s') -> Step(Raise(e1'),s')
      | Error -> Error
      | Stuck -> Stuck
    end
  | Try(e1,e2) ->
    begin match step e1 s with
      | Val(v1) -> Step(exp_of_val v1, s)
      | Error -> Step(e2,s)
      | Step(e1',s) -> Step(Try(e1',e2),s)
      | Stuck -> Stuck
    end

type store_ty = (loc * ty) list
[@@deriving show {with_path = false}]

let rec store_ty_lookup (l : loc) (st : store) : ty = match st with
  | [] -> raise NOT_FOUND
  | (l',t) :: st' -> if l = l' then t else store_ty_lookup l st'

(*  INFER *)
  let rec infer (e : exp) (st : store_ty) : ty = match e with
    | True -> Bool
    | False -> Bool
    | If(e1,e2,e3) ->
        let t1 = infer e1 st in
        let t2 = infer e2 st in
        let t3 = infer e3 st in
        if not (t1 = Bool) then raise TYPE_ERROR else
        if not (t2 = t3) then raise TYPE_ERROR else
          t2
    | Pair(e1,e2) ->
      let t1 = infer e1 st in
      let t2 = infer e2 st in
      Prod(t1,t2)
    | Projl(e1) ->
      let t1 = infer e1 st in
      begin match t1 with
      | Prod(t11,_) -> t11
      | _ -> raise TYPE_ERROR
      end
    | Projr(e1) ->
      let t1 = infer e1 st in
      begin match t1 with
      | Prod(_,t12) -> t12
      | _ -> raise TYPE_ERROR
      end
    | Raise(e1) ->
      let t1 = infer e1 st in
      begin match t1 with
      | Exp(t) -> t
      | _ -> TYPE_ERROR
      end
    | Try(e1,e2) ->
      let t1 = infer e1 st in
      let t2 = infer e2 st in
      if not (t1 = t2) then raise TYPE_ERROR
      t1
    | Loc(l) -> Ref(store_ty_lookup l st)
  end
