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
  | Error(e1)
    let t1 = infer e1 st in
    t1
  | Raise(e1)
    let t1 = infer e1 st in
    begin match t1 with
    | Exp(t) -> t
    | _ -> TYPE_ERROR
    end
  | Try(e1,e2)
    let t1 = infer e1 st in
    let t2 = infer e2 st in
    if not (t1 = t2) then raise TYPE_ERROR
    t1
  | TryWith(e1,e2)
    let t1 = infer e1 st in
    let t2 = infer e2 st in
    begin match t2 with
    | Exp(t) -> if (t1 = t) then t1 else raise TYPE_ERROR
    | _ -> raise TYPE_ERROR
end
