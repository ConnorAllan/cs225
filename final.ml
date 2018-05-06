(* Name: Connor Allan *)
(* Name: Aaron Longchamp *)
(* Course: UVM CS 225 Spring 2018 - Darais *)
(* Final Project *)

open Util
open StringSetMap


exception NOT_FOUND

(* Types.
 *
 * τ ∈ ty ⩴ bool
 *        | val
 *        | prod(ty,ty)
 *        | exp(ty) | ref(ty)
*)
type ty =
  | Bool
  | Val
  | Prod of ty * ty
  | Ref of ty
  | Exp of ty
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

let rec store_ty_lookup (l : loc) (st : store_ty) : ty = match st with
  | [] -> raise NOT_FOUND
  | (l',t) :: st' -> if l = l' then t else store_ty_lookup l st'

exception TYPE_ERROR

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
    Exp(t1)
  | Try(e1,e2) ->
    let t1 = infer e1 st in
    let t2 = infer e2 st in
    if not (t1 = t2) then raise TYPE_ERROR else
      t1
  | Loc(l) -> Ref(store_ty_lookup l st)

  let step_tests : test_block =
    let s1 : store = [(1,VTrue);(2,VFalse)] in
    TestBlock
    ( "STEP"
    , [ (True,s1)                                              , Val(VTrue)
      ; (False,s1)                                             , Val(VFalse)
      ; (If(True,False,True),s1)                               , Step(False,s1)
      ; (If(False,False,True),s1)                              , Step(True,s1)
      ; (If(Pair(True,False),True,False),s1)                   , Stuck
      ; (Pair(True,False),s1)                                  , Val(VPair(VTrue,VFalse))
      ; (Projl(Pair(True,False)),s1)                           , Step(True,s1)
      ; (Projl(True),s1)                                       , Stuck
      ; (Projl(If(True,Pair(True,False),Pair(False,True))),s1) , Step(Projl(Pair(True,False)),s1)
      ; (Projr(Pair(True,False)),s1)                           , Step(False,s1)
      ; (Projr(True),s1)                                       , Stuck
      ; (Projr(If(True,Pair(True,False),Pair(False,True))),s1) , Step(Projr(Pair(True,False)),s1)
      ; (Raise(True),s1)                                       , Step(True,s1)
      ; (Raise(Projr(True)),s1)                                , Stuck
      ; (Raise(If(True,Pair(False,True),False)),s1)            , Step(Raise(Pair(False,True)),s1)
      ; (Try(True,False),s1)                                   , Step(True,s1)
      ; (Try(If(True,Pair(True,False),False),Projl(True)),s1)  , Step(Try(Pair(True,False),Projl(True)),s1)
      ]
    , (fun (e,s) -> step e s)
    , [%show : exp * store]
    , [%show : result]
    )

let infer_tests =
  let st : store_ty = [(1,Bool);(2,Prod(Bool,Bool));(3,Ref(Bool))] in
  TestBlock
    ( "INFER"
    , [ True                                                 , Bool
      ; False                                                , Bool
      ; If(True,False,True)                                  , Bool
      ; Raise(True)                                          , Exp(Bool)
      ; Try(True,False)                                      , Bool
      ]
    , (fun e -> infer e st)
    , (fun e -> [%show : exp * store_ty] (e,st))
    , [%show : ty]
    )

let _ =
  _SHOW_PASSED_TESTS := false ;
  run_tests [step_tests;infer_tests]
