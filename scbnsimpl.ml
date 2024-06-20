type term =
  | Var of string
  | Lam of string * term
  | App of term * term

module SMap = Map.Make(String)

type value =
  | Clos of string * term * env * (string * value) option ref
  | Freevar of string
  | StructApp of value * value
  | Lazy of term * env
  | Blackhole

and env = value ref SMap.t

let fresh = let r = ref 0 in fun prefix -> incr r; prefix ^ string_of_int !r

let makelazy t e =
  match t with
  | Var x -> SMap.find x e
  | _ -> ref (Lazy (t, e))

let rec eval t e deep_flag =
  match t with
  | App (t1, t2) ->
    begin match eval t1 e false with
      | Lazy _ | Blackhole -> assert false
      | Clos (x, t0, e0, _) ->
        eval t0 (SMap.add x (makelazy t2 e) e0) deep_flag
      | v -> StructApp (v, eval t2 e true)
    end
  | Lam (x, t) ->
    let z =
      if deep_flag then
        let z = fresh ("_" ^ x ^ "_") in
        Some (z, eval t (SMap.add x (ref (Freevar z)) e) true)
      else
        None
    in
    Clos (x, t, e, ref z)
  | Var x ->
    let u = SMap.find x e in
    force deep_flag u; !u

and deepen v =
  match v with
  | Blackhole | Lazy _ -> assert false
  | Clos (x, t1, e1, n) when !n = None ->
    let z = fresh ("_" ^ x ^ "_") in
    n := Some (z, eval t1 (SMap.add x (ref (Freevar z)) e1) true)
  | _ -> ()

and force deep_flag v =
  match !v with
  | Lazy (t, e) -> v := Blackhole; let r = eval t e deep_flag in v := r
  | _ -> if deep_flag then deepen !v






type term =
  | Var of string
  | Lam of string * term
  | App of term * term

module SMap = Map.Make(String)

type value_ =
  | Clos of string * term * env * string * value
  | Freevar of string
  | StructApp of value_ * value_

and value = value_ Lazy.t

and env = value SMap.t

let fresh = let r = ref 0 in fun prefix -> incr r; prefix ^ string_of_int !r

let rec makelazy t e =
  match t with
  | Var x -> SMap.find x e
  | _ -> lazy (eval t e)

and eval t e =
  match t with
  | App (t1, t2) ->
    begin match eval t1 e with
    | Clos (x, t0, e0, _, _) ->
      eval t0 (SMap.add x (makelazy t2 e) e0)
    | v -> StructApp (v, eval t2 e)
    end
  | Lam (x, t) ->
    let z = fresh ("_" ^ x ^ "_") in
    Clos (x, t, e, z, lazy (eval t (SMap.add x (Lazy.from_val (Freevar z)) e)))
  | Var x ->
    Lazy.force (SMap.find x e)

let rec force_deep v =
  match v with
  | StructApp (v1, v2) -> force_deep v1; force_deep v2
  | Freevar _ -> ()
  | Clos (_, _, _, _, v) -> force_deep (Lazy.force v)
