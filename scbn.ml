type term =
  | Var of string
  | Lam of string * term
  | App of term * term
  | Constr of int * term list
  | Switch of term * (string list * term) list
  | Fix of string list * term

let rec size t =
  match t with
  | Var _ -> 1
  | Lam (_, t) -> 1 + size t
  | App (t1, t2) -> 1 + size t1 + size t2
  | Constr (_, l) -> List.fold_left (+) 1 (List.map size l)
  | Switch (t, l) ->
    List.fold_left (+) (1 + size t) (List.map (fun (vs, t1) -> List.length vs + size t1) l)
  | Fix (l, t) -> List.length l + size t

let size1 t =
  let ( +% ) (a, b) x = (a + x, b) in
  let ( ++ ) (a, b) (c, d) = (a + c, max b d) in
  let rec aux t =
    match t with
    | Var _ -> (1, 1)
    | Lam (_, t) -> let (a, b) = aux t in (1, max a b)
    | App (t1, t2) -> (aux t1 ++ aux t2) +% 1
    | Constr (_, l) ->
      List.fold_left (++) (1, 1) (List.map aux l)
    | Switch (t, l) ->
      List.fold_left (++) (aux t +% 1) (List.map (fun (vs, t1) -> aux t1 +% List.length vs) l)
    | Fix (l, t) -> let (a, b) = aux t +% List.length l in (1, max a b)
  in
  let (a, b) = aux t in
  max a b

module SMap = Map.Make(String)

type value =
  | Clos of string * term * env * (string * value) option ref
  | Freevar of string
  | StructApp of value * value
  | Lazy of term * env
  | Blackhole
  | Block of int * value ref list * bool ref (* is deep? *)
  | StructSwitch of value * (string list * value) list
  | StructFix of string list * term * env * (value ref * bool ref) list * int * (string list * value) option ref

and env = value ref SMap.t

let fresh = let r = ref 0 in fun prefix -> incr r; prefix ^ string_of_int !r

let betacnt = ref 0
let evalcnt = ref 0
let findcnt = ref 0

exception Timeout
let evalcnt_max = ref max_int

let makelazy t e =
  match t with
  | Var x -> SMap.find x e
  | _ -> ref (Lazy (t, e))

let rec eval t e deep_flag =
  incr evalcnt;
  if !evalcnt > !evalcnt_max then raise Timeout;
  match t with
  | App (t1, t2) ->
    begin match eval t1 e false with
      | Lazy _ | Blackhole -> assert false
      | Block _ -> assert false (* Typing error *)
      | Clos (x, t0, e0, _) ->
        incr betacnt;
        eval t0 (SMap.add x (makelazy t2 e) e0) deep_flag
      | StructFix (args, t0, e0, vals, 1, body) as v ->
        let arg = eval t2 e false in
        begin match arg with
          | Lazy _ | Blackhole -> assert false
          | Clos _ -> assert false (* Typing error *)
          | Block _ ->
            betacnt := !betacnt + List.length args;
            let vals =
              ref (StructFix (args, t0, e0, [], List.length args - 1, body)) ::
              List.rev (ref arg :: (List.map fst vals)) in
            let e1 = List.fold_left (fun e1 (name, v) -> SMap.add name v e1) e0 (List.combine args vals) in
            eval t0 e1 deep_flag
          | _ ->
            deepen arg; deepen v;
            StructApp (v, arg)
        end
      | StructFix (args, t0, e0, vals, i, body) ->
        assert (i > 1);
        if deep_flag then begin
          List.iter (fun (v, b) -> if not !b then begin force true v; b := true end) vals;
          let vals = (ref (eval t2 e true), ref true) :: vals in
          if !body = None then begin
            let nvars = List.map (fun name -> fresh ("_" ^ name ^ "_")) args in
            let e1 = List.fold_left
                (fun e1 (name1, name2) -> SMap.add name1 (ref (Freevar name2)) e1) e0 (List.combine args nvars) in
            body := Some (nvars, eval t0 e1 true)
          end;
          StructFix (args, t0, e0, vals, i - 1, body)
        end else begin
          StructFix (args, t0, e0, (makelazy t2 e, ref false) :: vals, i - 1, body)
        end
      | v -> StructApp (v, eval t2 e true)
    end
  | Lam (x, t) ->
    let z =
      if deep_flag then
        let z = fresh ("_" ^ x ^ "_") in
        (*let () = Format.eprintf "Normalizing function with argument name %s@." z in *)
        Some (z, eval t (SMap.add x (ref (Freevar z)) e) true)
      else
        None
    in
    Clos (x, t, e, ref z)
  | Var x ->
    incr findcnt;
    let u = SMap.find x e in
    force deep_flag u; !u
  | Constr (tag, l) ->
    if deep_flag then
      Block (tag, List.map (fun t -> ref (eval t e true)) l, ref true)
    else
      Block (tag, List.map (fun t -> makelazy t e) l, ref false)
  | Switch (t, l) ->
    begin match eval t e false with
      | Lazy _ | Blackhole -> assert false
      | Clos _ -> assert false (* Typing error *)
      | Block (tag, args, b) ->
        let (vars, t1) = List.nth l tag in
        assert (List.length vars = List.length args);
        let ne = ref e in
        List.iter2 (fun x v -> ne := SMap.add x v !ne) vars args;
        eval t1 !ne deep_flag
      | v ->
        let nl = List.map (fun (vars, t1) ->
            let nvars = List.map (fun name -> fresh ("_" ^ name ^ "_")) vars in
            let ne = ref e in
            List.iter2 (fun x z -> ne := SMap.add x (ref (Freevar z)) !ne) vars nvars;
            (nvars, eval t1 !ne true)
          ) l
        in
        StructSwitch (v, nl)
    end
  | Fix (args, t0) ->
    let z =
      if deep_flag then
        let nvars = List.map (fun name -> fresh ("_" ^ name ^ "_")) args in
        let e1 = List.fold_left
            (fun e1 (name1, name2) -> SMap.add name1 (ref (Freevar name2)) e1) e (List.combine args nvars) in
        Some (nvars, eval t0 e1 true)
      else
        None
    in
    StructFix (args, t0, e, [], List.length args - 1, ref z)


and deepen v =
  match v with
  | Blackhole | Lazy _ -> assert false
  | Clos (x, t1, e1, n) when !n = None ->
    let z = fresh ("_" ^ x ^ "_") in
    (* let () = Format.eprintf "Normalizing function with argument name %s@." z in *)
    n := Some (z, eval t1 (SMap.add x (ref (Freevar z)) e1) true)
  | Block (x, l, b) ->
    if not !b then begin
      List.iter (force true) l;
      b := true
    end
  | StructFix (args, t0, e0, vals, i, body) ->
    assert (i >= 1);
    List.iter (fun (v, b) -> if not !b then begin force true v; b := true end) vals;
    if !body = None then begin
      let nvars = List.map (fun name -> fresh ("_" ^ name ^ "_")) args in
      let e1 = List.fold_left
          (fun e1 (name1, name2) -> SMap.add name1 (ref (Freevar name2)) e1) e0 (List.combine args nvars) in
      body := Some (nvars, eval t0 e1 true)
    end
  | _ -> ()

and force deep_flag v =
  match !v with
  | Lazy (t, e) -> v := Blackhole; let r = eval t e deep_flag in v := r
  | _ -> if deep_flag then deepen !v

let rec eval_cbv t e deep_flag =
  incr evalcnt;
  match t with
  | App (t1, t2) ->
    begin match eval t1 e false with
      | Lazy _ -> assert false
      | Clos (x, t0, e0, _) ->
        incr betacnt;
        eval t0 (SMap.add x (ref (eval t2 e deep_flag)) e0) deep_flag
      | v -> StructApp (v, eval t2 e true)
    end
  | Lam (x, t) ->
    let z =
      if deep_flag then
        let z = fresh "_x" in
        Some (z, eval t (SMap.add x (ref (Freevar z)) e) true)
      else
        None
    in
    Clos (x, t, e, ref z)
  | Var x ->
    incr findcnt;
    let u = SMap.find x e in
    begin match !u with
      | Lazy (t1, e1) -> assert false
      | Clos (x, t1, e1, n) as v when deep_flag && !n = None ->
        let z = fresh "_x" in
        n := Some (z, eval t1 (SMap.add x (ref (Freevar z)) e1) true); v
      | v -> v
    end
  | _ -> assert false


let app f x = App (f, x)
let app2 f x y = app (app f x) y
let app3 f x y z = app (app2 f x y) z
let app4 f x y z w = app (app3 f x y z) w

let protect level1 print level2 ff v =
  if level1 > level2 then
    Format.fprintf ff "(%a)" (print level2) v
  else
    Format.fprintf ff "%a" (print level2) v

let rec print_value level ff v =
  match v with
  | Lazy _ -> Format.fprintf ff "<lazy>"
  | Blackhole -> Format.fprintf ff "<blackhole>"
  | Freevar x -> Format.fprintf ff "%s" x
  | StructApp (v1, v2) ->
    if level < 2 then Format.fprintf ff "(";
    Format.fprintf ff "%a %a" (print_value 2) v1 (print_value 1) v2;
    if level < 2 then Format.fprintf ff ")"
  | Clos (_, _, e, n) ->
    begin match !n with
      | None -> Format.fprintf ff "<function>"
      | Some v ->
        if level < 3 then Format.fprintf ff "(";
        Format.fprintf ff "\\%s. %a" (fst v) (print_value 3) (snd v);
        if level < 3 then Format.fprintf ff ")"
    end
  | Block (tag, l, _) ->
    Format.fprintf ff "[%d" tag;
    List.iter (fun v -> Format.fprintf ff " %a" (print_value 1) !v) l;
    Format.fprintf ff "]"
  | StructSwitch (v, l) ->
    Format.fprintf ff "match %a with " (print_value 3) v;
    List.iteri (fun tag (vars, t) ->
        Format.fprintf ff "| [%d" tag;
        List.iter (fun x -> Format.fprintf ff " %s" x) vars;
        Format.fprintf ff "] -> %a " (print_value 3) t
      ) l;
    Format.fprintf ff "end"
  | StructFix (_, _, _, vals, i, body) ->
    if level < 2 then Format.fprintf ff "(";
    assert (i >= 1);
    begin match !body with
      | None -> Format.fprintf ff "<fixfunction>"
      | Some v ->
        Format.fprintf ff "(fix %a. %a)"
          (Format.pp_print_list ~pp_sep:(fun ff () -> Format.fprintf ff " ") Format.pp_print_string) (fst v)
          (print_value 3) (snd v)
    end;
    List.iter (fun v -> Format.fprintf ff " %a" (print_value 1) !v) (List.map fst (List.rev vals));
    if level < 2 then Format.fprintf ff ")"

(*
and print_env ff e =
  SMap.iter (fun x v -> Format.fprintf ff "[%s := %a]" x (print_value 3) !v) e
*)
(* let () = Format.printf "%a@." (print_value 3) (runtest1 5) *)

let print v = Format.printf "%a@." (print_value 3) v

let run ?(free=[]) ?(deep=true) t =
  betacnt := 0; evalcnt := 0; findcnt := 0;
  let r = eval t (List.fold_left (fun m x -> SMap.add x (ref (Freevar x)) m) SMap.empty free) deep in
  Format.printf "Beta: %d, Find: %d, Total: %d, Size: %d, Beta*size: %d@." !betacnt !findcnt !evalcnt (size1 t) (!betacnt * size1 t);
  r

let run_cbv ?(free=[]) ?(deep=true) t =
  betacnt := 0; evalcnt := 0; findcnt := 0;
  let r = eval_cbv t (List.fold_left (fun m x -> SMap.add x (ref (Freevar x)) m) SMap.empty free) deep in
  Format.printf "Beta: %d, Find: %d, Total: %d, Size: %d, Beta*size: %d@." !betacnt !findcnt !evalcnt (size1 t) (!betacnt * size1 t);
  r

let run_and_print ?free ?deep t =
  print (run ?free ?deep t)

let rec test1 n =
  let x, y = fresh "x", fresh "y" in
  if n = 0 then Lam (x, Lam (y, App (App (Var y, Var x), Var x)))
  else Lam (x, App (test1 (n - 1), Lam (y, App (App (Var y, Var x), Var x))))

let runtest1 n =
  let z = fresh "z" in
  run (App (test1 n, Lam (z, Var z)))

let rec test2 n =
  let x = fresh "x" in
  if n = 0 then Var "y" else app (Lam (x, app (Var x) (Var x))) (test2 (n - 1))

let runtest2 n =
  run ~free:["y"] (test2 n)

let church n =
  let f, x = fresh "f", fresh "x" in
  let rec aux n = if n = 0 then Var x else App (Var f, aux (n - 1)) in
  Lam (f, Lam (x, aux n))

let church_succ =
  let n, f, x = fresh "n", fresh "f", fresh "x" in
  Lam (n, Lam (f, Lam (x, app2 (Var n) (Var f) (app (Var f) (Var x)))))

let church_add =
  let m, n, f, x = fresh "m", fresh "n", fresh "f", fresh "x" in
  Lam (m, Lam (n, Lam (f, Lam (x, app2 (Var m) (Var f) (app2 (Var n) (Var f) (Var x))))))

let church_mul =
  let m, n, f = fresh "m", fresh "n", fresh "f" in
  Lam (m, Lam (n, Lam (f, app (Var m) (app (Var n) (Var f)))))

let church_pow =
  let m, n = fresh "m", fresh "n" in
  Lam (m, Lam (n, app (Var n) (Var m)))

let church_pred =
  let n, f, x, g, h, u = fresh "n", fresh "f", fresh "x", fresh "g", fresh "h", fresh "u" in
  Lam (n, Lam (f, Lam (x, app3 (Var n) (Lam (g, Lam (h, app (Var h) (app (Var g) (Var f))))) (Lam (u, Var x)) (Lam (u, Var u)))))

let church_fact =
  let nxt = Lam ("p", app (Var "p") (Lam ("a", Lam ("b", Lam ("z", app2 (Var "z") (app church_succ (Var "a")) (app2 church_mul (Var "a") (Var "b"))))))) in
  Lam ("n", app3 (Var "n") nxt (Lam ("u", app2 (Var "u") (church 1) (church 1))) (Lam ("c", Lam ("d", Var "d"))))

let church_is_even =
  Lam ("n", app2 (Var "n") (Lam ("b", Lam ("x", Lam ("y", app2 (Var "b") (Var "y") (Var "x"))))) (Lam ("x", Lam ("y", Var "x"))))

let rec peano n =
  if n = 0 then
    Constr (0, [])
  else
    Constr (1, [peano (n - 1)])

let peano_add =
  Fix (["add"; "n"], Lam ("m", Switch (Var "n", [([], Var "m"); (["n1"], Constr (1, [app2 (Var "add") (Var "n1") (Var "m")]))])))

let peano_mul pa =
  Fix (["mul"; "n"], Lam ("m", Switch (Var "n", [([], Constr (0, [])); (["n1"], app2 pa (Var "m") (app2 (Var "mul") (Var "n1") (Var "m")))])))

let peano_fact pm =
  Fix (["fact"; "n"], Switch (Var "n", [([], peano 1); (["n1"], app2 pm (Var "n") (app (Var "fact") (Var "n1")))]))

let boom = Lam ("x", Var "x")

let nth =
  Fix (["nth"; "l"; "n"], Switch (Var "l", [([], boom); (["x"; "t"], Switch (Var "n", [([], Var "x"); (["n1"], app2 (Var "nth") (Var "t") (Var "n1"))]))]))

let eval_db =
  Fix (["eval"; "t"], Lam ("l", Switch (Var "t", [(["i"], app2 nth (Var "l") (Var "i")); (["t1"], Lam ("x", app2 (Var "eval") (Var "t1") (Constr (1, [Var "x"; Var "l"])))); (["t1"; "t2"], App (app2 (Var "eval") (Var "t1") (Var "l"), app2 (Var "eval") (Var "t2") (Var "l")))])))

let rec env_find_index x l =
  match l with
  | [] -> raise Not_found
  | y :: t -> if x = y then 0 else 1 + env_find_index x t
let rec db_encode t e =
  match t with
  | Var x -> Constr (0, [peano (env_find_index x e)])
  | Lam (x, t) -> Constr (1, [db_encode t (x :: e)])
  | App (t1, t2) -> Constr (2, [db_encode t1 e; db_encode t2 e])
  | _ -> assert false

(*
let () = run_and_print (app church_succ (church 4))
let () = run_and_print (app2 church_add (church 3) (church 4))
let () = run_and_print (app2 church_mul (church 1) (church 2))
let () = run_and_print (app2 church_mul (church 3) (church 4))
let () = run_and_print (app2 church_pow (church 2) (church 3))
let () = run_and_print (app church_pred (church 5))
let () = run_and_print (app church_fact (church 4))
let () = run_and_print (app2 peano_add (peano 3) (peano 4))
let () = run_and_print (app peano_add (peano 3))
let () = run_and_print (Lam ("x", app2 peano_add (Var "x") (peano 3)))
let () = run_and_print (app (Lam ("pa", Lam ("x", app2 (Var "pa") (app2 (Var "pa") (Var "x") (Var "x")) (peano 3)))) peano_add)
let () = run_and_print (app2 (peano_mul peano_add) (peano 3) (peano 4))
let () = run_and_print (app (Lam ("pa", app (peano_mul (Var "pa")) (peano 3))) peano_add)
let () = run_and_print (Lam ("x", app2 (peano_mul peano_add) (Var "x") (peano 3)))
let () = run_and_print (app (Lam ("pa", Lam ("x", Lam ("y", app2 (peano_mul (Var "pa")) (app2 (Var "pa") (peano 2) (Var "x")) (app2 (Var "pa") (peano 3) (Var "y")))))) peano_add)
let () = run_and_print (app (peano_fact (peano_mul peano_add)) (peano 4))
let () = run_and_print (peano_fact (peano_mul peano_add))
let () = run_and_print (Lam ("n", Switch (app2 peano_add (Constr (1, [Var "n"])) (Constr (0, [])), [([], Lam ("x", Var "x")); (["n"], Var "n")])))

let () = run_and_print (app2 eval_db (db_encode church_add []) (Constr (0, [])))
let () = run_and_print (app2 eval_db (db_encode (app2 church_add (church 3) (church 4)) []) (Constr (0, [])))
let () = run_and_print (app2 eval_db (db_encode church_fact []) (Constr (0, [])))
let () = run_and_print (app2 eval_db (db_encode (app church_fact (church 4)) []) (Constr (0, [])))
let () = run_and_print (Lam ("l", app2 eval_db (db_encode (Lam ("x", App (Var "x", Var "y"))) ["y"]) (Var "l")))
let () = run_and_print eval_db
*)
let compile1_prelude = "
  type nf = Var of string | Lam of nf * nf | App of nf * nf
  type prenf = Nf of nf | Prevar of string
  type l = Lazy of (bool -> v) | Forward of v | Blackhole
  and v = (bool -> l ref -> v) * prenf ref
  let mklazy f = ref (Lazy f)
  let mkval v = ref (Forward v)
  let getnf v = match !(snd v) with Nf nf -> nf | _ -> assert false
  let rec mkacc v =
    ((fun _ arg -> mkacc (App (v, getnf (lazy_force arg true)))), ref (Nf v))
  and mkaccl v = mkval (mkacc v)
  and lazy_force x b =
    match !x with
    | Lazy f -> x := Blackhole; let r = f b in x := Forward r; r
    | Blackhole -> assert false
    | Forward (v, nf) ->
      if b then begin match !nf with
      | Prevar s ->
        let x = Var s in
        nf := Nf (Lam (x, getnf (v true (mkaccl x))))
      | _ -> ()
      end; (v, nf)
  let mklam f name b = if b then let x = Var name in (f, ref (Nf (Lam (x, getnf (f true (mkaccl x)))))) else (f, ref (Prevar name))
  let rec print ff t =
    match t with
    | Var s -> Format.fprintf ff \"%s\" s
    | Lam (x, t) -> Format.fprintf ff \"(\\\\%a.%a)\" print x print t
    | App (t1, t2) -> Format.fprintf ff \"(%a %a)\" print t1 print t2

"
type deep_flag = Shallow | Deep | Unknown
let compile_flag ff df = match df with
  | Shallow -> Format.fprintf ff "false"
  | Deep -> Format.fprintf ff "true"
  | Unknown -> Format.fprintf ff "df"
let rec compile1 ff (df, t) =
  match t with
  | Var x ->
    begin match df with
      | Shallow -> Format.fprintf ff "(fst (lazy_force %s false))" x
      | Deep -> Format.fprintf ff "(getnf (lazy_force %s true))" x
      | Unknown -> Format.fprintf ff "(lazy_force %s df)" x
    end
  | Lam (x, t) ->
    begin match df with
      | Shallow -> Format.fprintf ff "(fun df %s -> %a)" x compile1 (Unknown, t)
      | Deep -> Format.fprintf ff "(let %s = Var %S in Lam (%s, %a))" x x x compile1 (Deep, t)
      | Unknown -> Format.fprintf ff "(mklam (fun df %s -> %a) %S df)" x compile1 (Unknown, t) x
    end
  | App (t1, t2) ->
    let print2 ff =
      match t2 with
      | Var x -> Format.fprintf ff "%s" x
      | Lam (x, t) -> Format.fprintf ff "(mkval ((fun df %s -> %a), ref (Prevar %S)))" x compile1 (Unknown, t) x
      | _ -> Format.fprintf ff "(mklazy (fun df -> %a))" compile1 (Unknown, t2)
    in
    begin match df with
      | Shallow -> Format.fprintf ff "(fst (%a false %t))" compile1 (Shallow, t1) print2
      | Deep -> Format.fprintf ff "(getnf (%a true %t))" compile1 (Shallow, t1) print2
      | Unknown -> Format.fprintf ff "(%a df %t)" compile1 (Shallow, t1) print2
    end
  | _ -> assert false

let compile ff t =
  Format.fprintf ff "let result = %a let () = Format.printf \"%%a@@.\" print result" compile1 (Deep, t)

let () = Format.printf "%s@." compile1_prelude
let c t = Format.printf "%a@." compile t
let cn t = Format.printf "let result = %a" compile1 (Deep, t)
let () = c (app church_succ (church 4))
let () = c (app2 church_pow (church 10) (church 2))
let () = c (app church_is_even (app2 church_pow (church 10) (church 7)))
let () = cn (app2 church_pow (church 10) (church 5))
(* let () = ignore (run (app2 church_pow (church 10) (church 4))) *)


let () = Random.init 42
let rec randterm n l =
  if n = 0 then
    if l = [] then Lam ("z", Var "z")
    else Var (List.nth l (Random.int (List.length l)))
  else if Random.int 1000 < 500 then
    let x = fresh "x" in Lam (x, randterm (n - 1) (x :: l))
  else
    let k = Random.int n in
    App (randterm k l, randterm (n - k - 1) l)

(*
let rec print_eole_term ff t =
  match t with
  | Var x -> Format.fprintf ff "%sA" x
  | Lam (x, t) -> Format.fprintf ff "(%sA->%a)" x print_eole_term t
  | App (t1, t2) -> Format.fprintf ff "(%a %a)" print_eole_term t1 print_eole_term t2
  | _ -> assert false

let rec print_eole_result ff v =
  match v with
  | Lazy _ | Blackhole | Block _ | StructSwitch _ -> assert false
  | Freevar x -> Format.fprintf ff "%s" x
  | StructApp (v1, v2) ->
    Format.fprintf ff "(%a %a)" print_eole_result v1 print_eole_result v2
  | Clos (_, _, e, n) ->
    begin match !n with
      | None -> assert false
      | Some v ->
        Format.fprintf ff "(%s->%a)" (fst v) print_eole_result (snd v);
    end

let result_size r =
  let l = ref [] in
  let rec aux v =
    match List.assq v !l with
    | x -> x
    | exception Not_found ->
      let s =
        match v with
        | Freevar _ -> 1
        | StructApp (v1, v2) -> 1 + aux v1 + aux v2
        | Clos (_, _, _, n) -> (match !n with None -> assert false | Some v -> 1 + aux (snd v))
        | _ -> assert false
      in
      l := (v, s) :: !l; s
  in aux r

let is_result_big r =
  let c = ref 0 in
  let rec aux v =
    if !c > 100000 then raise Exit;
    match v with
    | Freevar _ -> incr c
    | StructApp (v1, v2) -> incr c; aux v1; aux v2
    | Clos (_, _, _, n) -> (match !n with None -> assert false | Some v -> incr c; aux (snd v))
    | _ -> assert false
  in
  try aux r; false with Exit -> true


let run_diverging i t =
  let mxred = 100000 in
  let old = !evalcnt_max in
  evalcnt_max := mxred;
  begin match run t with
    | r ->
      if is_result_big r then
        Format.printf "Result too big to print@."
      else begin
        let f = open_out ("eole_test/test_" ^ string_of_int i ^ ".in") in
        Format.fprintf (Format.formatter_of_out_channel f) "%a.@." print_eole_term t;
        close_out f;
        let f = open_out ("eole_test/test_" ^ string_of_int i ^ ".out") in
        Format.fprintf (Format.formatter_of_out_channel f) "%a@." print_eole_result r;
        close_out f
      end
    | exception Timeout -> Format.printf "Timeout@."
  end;
  evalcnt_max := old

let () =
  for i = 1 to 10000 do
    run_diverging i (randterm 1000 []);
  done
*)




(*
let () = run_and_print (app church_succ (church 4))
let () = run_and_print (app2 church_add (church 3) (church 4))
let () = run_and_print (app2 church_mul (church 1) (church 2))
let () = run_and_print (app2 church_mul (church 3) (church 4))
let () = run_and_print (app2 church_pow (church 2) (church 3))
let () = run_and_print (app church_pred (church 5))
let () = run_and_print (app church_fact (church 4))

let loop = let x = fresh "x" in let u = Lam (x, App (Var x, Var x)) in App (u, u)

let () = run_and_print (App (Lam ("z", Lam ("x", Var "x")), loop))

let () = print (runtest1 3)
let () = ignore (runtest1 1000)
let () = print (runtest2 3)
let () = ignore (runtest2 1000)

let () = ignore (run (app2 church_mul (church 1000) (church 1000)))
let () = ignore (run (app2 church_mul (church 300) (church 300)))
let () = ignore (run (Lam ("x", Lam ("y", app2 church_mul (app2 church_add (church 100) (Var "x")) (app2 church_add (church 100) (Var "y"))))))
let () = ignore (run (Lam ("x", Lam ("y", app2 church_mul (app2 church_add (church 300) (Var "x")) (app2 church_add (church 300) (Var "y"))))))


let () = ignore (run (app2 church_mul (church 256) (church 64)))
let () = ignore (run (app2 church_mul (church 64) (church 256)))
let () = ignore (run (Lam ("x", Lam ("y", app2 church_mul (app2 church_add (church 128) (Var "x")) (app2 church_add (church 128) (Var "y"))))))
(* let () = ignore (run (app church_fact (church 9))) *)
let () = ignore (run (app2 church_pow (church 10) (church 7)))
*)

(* let () = ignore (run (app2 church_pow (church 10) (church 4))) *)
(* let () = ignore (run (app2 church_mul (church 100) (church 300))) *)
(* let () = ignore (run (app2 church_pow (church 10) (church 6))) *)
(* let () = ignore (run_cbv (app2 church_mul (church 1000) (church 1000))) *)
(* let () = run_and_print (app church_is_even (app2 church_pow (church 10) (church 6))) *)
(* let () = run_and_print (app church_is_even (app2 church_mul (church 1000) (church 1000))) *)

(*

let rec eval_open t e =
  match t with
  | App (t1, t2) ->
    begin match eval_open t1 e with
      | Lazy _ -> assert false
      | Clos (x, t0, e0, _) ->
        eval_open t0 (SMap.add x (ref (Lazy (t2, e))) e0)
      | v -> StructApp (v, eval_open t2 e)
    end
  | Lam (x, t) ->
    Clos (x, t, e, ref None)
  | Var x ->
    let u = SMap.find x e in
    begin match !u with
      | Lazy (t1, e1) -> let r = eval_open t1 e1 in u := r; r
      | v -> v
    end

let blc_true = Lam ("x", Lam ("y", Var "x"))
let blc_false = Lam ("x", Lam ("y", Var "y"))
let blc_nil = blc_false
let blc_pair u v = let z = fresh "z" in Lam (z, app2 (Var z) u v)
let blc_Y = Lam ("f", app (Lam ("x", app (Var "x") (Var "x"))) (Lam ("x", app (Var "f") (app (Var "x") (Var "x")))))
let blc_bool b = if b then blc_true else blc_false
let rec blc_seq l = match l with [] -> blc_nil | x :: t -> blc_pair x (blc_seq t)
let rec blc_seq_open l z = match l with [] -> z | x :: t -> blc_pair x (blc_seq_open t z)
let print_bool_list ff l =
  List.iter (fun b -> Format.fprintf ff (if b then "1" else "0")) l
let rec rep n x = if n = 0 then [] else x :: rep (n - 1) x
let rec env_find_index x l =
  match l with
  | [] -> raise Not_found
  | y :: t -> if x = y then 0 else 1 + env_find_index x t
let rec blc_encode t e =
  match t with
  | Var x -> rep (env_find_index x e + 1) true @ [false]
  | Lam (x, t) -> [false; false] @ blc_encode t (x :: e)
  | App (t1, t2) -> [false; true] @ blc_encode t1 e @ blc_encode t2 e
let rec blc_decode l e =
  match l with
  | false :: false :: l1 ->
    let x = fresh "w" in
    let t, l2 = blc_decode l1 (x :: e) in
    Lam (x, t), l2
  | false :: true :: l1 ->
    let t1, l2 = blc_decode l1 e in
    let t2, l3 = blc_decode l2 e in
    App (t1, t2), l3
  | true :: l1 ->
    let rec aux l e =
      match l, e with
      | true :: l1, _ :: e1 -> aux l1 e1
      | false :: l1, x :: _ -> Var x, l1
      | _ -> assert false
    in
    aux l1 e
  | _ -> assert false

let string_to_bool_list s =
  let rec aux i =
    if i = String.length s then [] else (s.[i] = '1') :: aux (i + 1)
  in aux 0

let blc_self, l = blc_decode (string_to_bool_list "0101000110100000000101011000000000011110000101111110011110000101110011110000001111000010110110111001111100001111100001011110100111010010110011100001101100001011111000011111000011100110111101111100111101110110000110010001101000011010") []
let () = assert (l = [])

let blc_encode_term_open t z =
  blc_seq_open (List.map blc_bool (blc_encode t [])) z

let blc_unpair t =
  match t with
  | Clos (x, t, e, _) ->
    let z = fresh "_z" in
    let v = eval_open t (SMap.add x (ref (Freevar z)) e) in
    (match v with
     | StructApp (StructApp (Freevar z1, v1), v2) when z1 = z -> Some (v1, v2)
     | Clos _ -> None
     | _ -> assert false)
  | _ -> assert false

let rec blc_unlist t =
  match blc_unpair t with
  | None -> []
  | Some (v1, v2) -> v1 :: blc_unlist v2

let blc_unbool t =
  match t with
  | Clos (x1, t1, e1, _) ->
    let z1 = fresh "_z" in
    let v1 = eval_open t1 (SMap.add x1 (ref (Freevar z1)) e1) in
    (match v1 with
     | Clos (x2, t2, e2, _) ->
       let z2 = fresh "_z" in
       let v2 = eval_open t2 (SMap.add x2 (ref (Freevar z2)) e2) in
       (match v2 with
        | Freevar z when z = z1 -> true
        | Freevar z when z = z2 -> false
        | _ -> assert false
       )
     | _ -> assert false)
  | _ -> assert false

let blc_selfeval_result = eval (app2 blc_self (Lam ("u", Var "u")) (blc_encode_term_open (Lam ("x", Var "x")) blc_nil)) SMap.empty false
(* let () = run_and_print ~deep:false blc_selfeval_result *)
let () = Format.printf "%a@." print_bool_list (List.map blc_unbool (blc_unlist blc_selfeval_result))
*)
