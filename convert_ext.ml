let debug = false
let count = true

let steps = ref 0

type term =
  | Var of string
  | Lam of string * term
  | App of term * term
  | Constr of int * term list
  | Switch of term * (string list * term) list
  | Fix of string * string list * term

module SMap = Map.Make(String)

type cont =
  | KId
  | KApp of valptr * cont
  | KSwitch of (string list * term) list * env * (string list * valptr) list * cont
  | KFix of string * term * env * valptr * cont

and neutral = string * cont * (valptr * int) option

and value =
  (*  | Lazy of term * env *)
  | Thread of rthread
  | Neutral of neutral
  | Clos of string * term * env * string * valptr
  | Block of int * valptr list
  | Fixpoint of string list * term * env * string * string list * valptr * valptr list

and valptr = {
  mutable value : value ;
  vid : int ;
}

and env = valptr SMap.t

and rthread = {
  mutable code : code ;
  mutable env : env ;
  mutable cont : cont ;
  self : valptr ;
  mutable rchild : rthread option ;
  mutable nblocking : int ;
  mutable blocking : thread list ;

  (* For debugging purposes *)
  rid : int ;
  mutable dead : bool ;
}

and code =
  | Term of term
  | Val of valptr

and cthread = {
  mutable desc : cthread_desc ;
  mutable parents : cthread list ;
  mutable running_parents : int ;
  mutable running : bool ;
  (* For debugging only *)
  cid : int ;
}

and cthread_desc =
  | CDone of bool
  | CVals of { t1 : valptr; t2 : valptr; mutable cchild : rthread option; varmap : string SMap.t }
  | CAnd of cthread * cthread
  | CPar of cthread * cthread
  | CParOr of cthread * cthread
  | CSame of cthread

and thread =
  | Reduce of rthread
  | Convert of cthread

let pp_list f ff l =
  Format.fprintf ff "[%a]" (Format.pp_print_list ~pp_sep:(fun ff () -> Format.fprintf ff "; ") f) l

let rec pp_term_at level ff t =
  let show lvl =
    if level >= lvl then begin
      Format.fprintf ff
    end else begin
      Format.fprintf ff "("; Format.kfprintf (fun ff -> Format.fprintf ff ")") ff
    end
  in
  match t with
  | Var x -> show 0 "%s" x
  | Lam (x, t) -> show 2 "λ%s. %a" x (pp_term_at 2) t
  | App (t1, t2) -> show 1 "%a %a" (pp_term_at 1) t1 (pp_term_at 0) t2
  | Constr (n, []) -> show 0 "#%d" n
  | Constr (n, l) ->
    show 1 "#%d %a" n
      (Format.pp_print_list ~pp_sep:(fun ff () -> Format.fprintf ff " ") (pp_term_at 0)) l
  | Switch (t, l) ->
    show 2 "match %a with%t" (pp_term_at 2) t
      (fun ff ->
         List.iteri (fun i (v, t) ->
             Format.fprintf ff " | #%d" i;
             List.iter (Format.fprintf ff " %s") v;
             Format.fprintf ff " -> %a" (pp_term_at 2) t) l)
  | Fix (f, l, t) ->
    show 2 "fix %s %a := %a end" f
      (Format.pp_print_list ~pp_sep:(fun ff () -> Format.fprintf ff " ") Format.pp_print_string) l
      (pp_term_at 2) t

let pp_term = pp_term_at 2

let pp_rthreadid ff t = Format.fprintf ff "Thread@%d" t.rid
let pp_cthreadid ff t = Format.fprintf ff "Thread@%d" t.cid
let pp_threadid ff t =
  match t with
  | Reduce t -> pp_rthreadid ff t
  | Convert t -> pp_cthreadid ff t

let pp_child ff t =
  match t with
  | None -> Format.fprintf ff "None"
  | Some t -> Format.fprintf ff "Some %a" pp_rthreadid t

let rec pp_value ff v =
  match v with
  (* | Lazy (t, _) -> Format.fprintf ff "lazy (%a)" pp_term t *)
  | Thread t -> pp_rthreadid ff t
  | Neutral (hd, k, _) ->
    pp_cont (fun ff -> Format.fprintf ff "%s" hd) ff k
  | Clos (x, t, _, _, _) -> Format.fprintf ff "clos %s.(%a)" x pp_term t
  | Block (tag, l) ->
    Format.fprintf ff "#%d" tag;
    List.iter (fun v -> Format.fprintf ff " (%a)" pp_value v.value) l
  | Fixpoint (args, t, _, _, _, _, l) ->
    Format.fprintf ff "(fix %a.(%a)) %a"
      (Format.pp_print_list ~pp_sep:(fun ff () -> Format.fprintf ff " ") Format.pp_print_string) args
      pp_term t
      (Format.pp_print_list ~pp_sep:(fun ff () -> Format.fprintf ff " ") pp_value) (List.map (fun v -> v.value) l)

and pp_cont base ff k =
  match k with
  | KId -> base ff
  | KApp (v, k) -> Format.fprintf ff "%a (%a)" (pp_cont base) k pp_value v.value
  | KSwitch (l, _, _, k) ->
    Format.fprintf ff "match %a with%t" (pp_cont base) k
      (fun ff ->
         List.iteri (fun i (v, t) ->
             Format.fprintf ff " | #%d" i; List.iter (Format.fprintf ff " %s") v; Format.fprintf ff " -> %a" pp_term t) l)
  | KFix (s, t, _, _, k) ->
    Format.fprintf ff "(fix %s. %a) (%a)" s pp_term t (pp_cont base) k

let pp_code ff c =
  match c with
  | Term t -> Format.fprintf ff "Term (%a)" pp_term t
  | Val v -> Format.fprintf ff "Val (%a)" pp_value v.value

let pp_rthread ff t =
  if not t.dead then
  Format.fprintf ff "Thread@%d = { code = %a ; cont = %a ; rchild = %a ; nblocking = %d ; blocking = %a }@."
    t.rid
    pp_code t.code
    (pp_cont (fun ff -> Format.fprintf ff "[]")) t.cont
    pp_child t.rchild
    t.nblocking
    (pp_list pp_threadid) t.blocking

let pp_cthread_desc ff desc =
  match desc with
  | CVals { t1; t2; varmap = _; cchild } ->
    Format.fprintf ff "CVals { t1 = %a ; t2 = %a ; cchild = %a }"
    pp_value t1.value
    pp_value t2.value
    pp_child cchild
  | CDone b -> Format.fprintf ff "CDone %b" b
  | CAnd (t1, t2) -> Format.fprintf ff "CAnd (%a, %a)" pp_cthreadid t1 pp_cthreadid t2
  | CPar (t1, t2) -> Format.fprintf ff "CPar (%a, %a)" pp_cthreadid t1 pp_cthreadid t2
  | CParOr (t1, t2) -> Format.fprintf ff "CParOr (%a, %a)" pp_cthreadid t1 pp_cthreadid t2
  | CSame t -> Format.fprintf ff "CSame %a" pp_cthreadid t

let pp_cthread ff t =
  Format.fprintf ff "Thread@%d = { running = %b ; desc = %a ; parents = %a }@."
    t.cid
    t.running
    pp_cthread_desc t.desc
    (pp_list pp_cthreadid) t.parents

let freshid = let r = ref 0 in fun () -> incr r; !r

let tls = ref []
let register_thread t = if debug then tls := t :: !tls
let register_rthread t = register_thread (Reduce t)
let register_cthread t = register_thread (Convert t)





type 'a nthread =
  {
    tid : int ;
    mutable tparents : any_thread list ;
    mutable tchildren : any_thread list ;
  }

and any_thread = AnyThread : 'a nthread -> any_thread [@@unboxed]

(* API:
   - pause (recursive)
   (* - cancel (recursive) *)
   - start/resume
*)







(*
let cthreads_tbl = Hashtbl.create 17
let rthread_tbl = Hashtbl.create 17
let thread_queue = Queue.create ()

let push_rthread t =
  Queue.push (Reduce t) thread_queue

let push_cthread t =
  Queue.push (Convert t) thread_queue

let push_list l = List.iter (fun t -> Queue.push t thread_queue) l

let pop_thread () =
  Queue.take_opt thread_queue
*)
let empty_queue = ([], [])
let is_empty queue = queue = ([], [])
let push_back (q1, q2) x = (q1, x :: q2)
let push_front (q1, q2) x = (x :: q1, q2)
let push_back_list (q1, q2) l = (q1, List.rev_append l q2)
let push_front_list (q1, q2) l = (List.append l q1, q2)
let pop_front (q1, q2) =
  match q1 with
  | x :: q -> Some (x, (q, q2))
  | [] ->
    match List.rev q2 with
    | x :: q -> Some (x, (q, []))
    | [] -> None

let mkvalptr v =
  { value = v ; vid = freshid () }

let start_lazy a u e =
  let rt = { code = Term u; env = e; cont = KId; self = a; blocking = []; nblocking = 0; rchild = None; rid = freshid () ; dead = false } in
  register_rthread rt;
  a.value <- Thread rt;
  rt

let dummy_value = Neutral ("", KId, None)
let makelazy t e =
  match t with
  | Var x -> SMap.find x e
  | _ -> (* mkvalptr (Lazy (t, e)) *)
    let a = mkvalptr dummy_value in
    ignore (start_lazy a t e);
    a

let rec unneeded t =
  t.nblocking <- t.nblocking - 1;
  if t.nblocking = 0 then begin
    t.blocking <- [];
    begin match t.rchild with
      | Some nt -> t.rchild <- None; unneeded nt
      | None -> ()
    end
  end

let rec stop_cthread t parent =
  (* t.parents <- List.filter (fun p -> p != parent) t.parents; *)
  t.running_parents <- t.running_parents - 1;
  if t.running && (* t.parents = [] *) t.running_parents = 0 then begin
    t.parents <- [];
    t.running <- false;
    stop_cthread_desc t.desc t
  end

and stop_cthread_desc desc t =
  match desc with
  | CVals ({ cchild = Some rt; _ } as vls) ->
    vls.cchild <- None; unneeded rt
  | CVals { cchild = None; _ } | CDone _ -> ()
  | CAnd (c1, c2) | CPar (c1, c2) | CParOr (c1, c2) ->
    stop_cthread c1 t; stop_cthread c2 t
  | CSame c -> stop_cthread c t

let exit_thread t result rest =
  t.self.value <- result;
  t.dead <- true;
  List.iter (function
      | Reduce nt -> nt.rchild <- None
      | Convert nt ->
        match nt.desc with
        | CVals ({ cchild = Some _; _} as vls) -> vls.cchild <- None
        | _ -> ()) t.blocking;
  push_front_list rest t.blocking

exception Result of bool

let rec exit_cthread t result =
  let parents = t.parents in
  t.parents <- [];
  (* t.running_parents <- 0; *)
  let desc = t.desc in
  t.desc <- CDone result;
  t.running <- false;
  stop_cthread_desc desc t;
  List.iter check_exit parents

and check_exit t =
  if t.running then begin
    match t.desc with
    | CVals _ | CDone _ -> ()
    | CAnd ({ desc = CDone false; _}, _) | CAnd (_, { desc = CDone false; _}) ->
      exit_cthread t false
    | CAnd ({ desc = CDone true; _}, { desc = CDone true; _}) ->
      exit_cthread t true
    | CPar ({ desc = CDone b; _}, _) | CPar (_, { desc = CDone b; _}) ->
      exit_cthread t b
    | CParOr ({ desc = CDone b; _}, _) ->
      exit_cthread t b
    | CParOr (_, { desc = CDone true; _ }) ->
      exit_cthread t true
    | CSame { desc = CDone b } ->
      exit_cthread t b
    | _ -> ()
  end

let fresh =
  let r = ref 0 in
  fun prefix -> incr r; prefix ^ "@" ^ string_of_int !r

let wait_for t rt rest =
  rt.blocking <- t :: rt.blocking;
  rt.nblocking <- rt.nblocking + 1;
  begin match t with
    | Reduce t -> assert (t.rchild = None); t.rchild <- Some rt
    | Convert { desc = CVals vls; _ } ->
      assert (vls.cchild = None); vls.cchild <- Some rt
    | Convert _ -> assert false
  end;
  if rt.nblocking = 1 then push_front rest (Reduce rt) else rest

let print_all () =
  List.iter (function Reduce t -> Format.printf "%a" pp_rthread t | Convert t -> Format.printf "%a" pp_cthread t) !tls

let cthreads_memo = Hashtbl.create 17


let rec maybe_resume t parent rest =
  if parent.running_parents > 0 then begin
  t.parents <- parent :: t.parents;
  let n = t.running_parents in
  t.running_parents <- n + 1;
  if n = 0 then resume_cthread t rest else rest
  end else rest

and resume_cthread t rest =
  t.running <- true;
  match t.desc with
  | CDone b ->
    let parents = t.parents in
    t.parents <- [];
    t.running_parents <- 0;
    t.running <- false;
    List.iter check_exit parents;
    rest
  | CAnd (t1, t2) | CPar (t1, t2) | CParOr (t1, t2) ->
    let rest = maybe_resume t1 t rest in maybe_resume t2 t rest
  | CSame t1 -> maybe_resume t1 t rest
  | CVals { t1; t2; varmap; cchild = None; } ->
    push_back rest (Convert t)
  | CVals { t1; t2; varmap; cchild = Some rt } ->
    assert false


let mkcthread_desc desc rest =
  let t = { desc; running = true; running_parents = 0; parents = []; cid = freshid () } in
  register_cthread t;
  let rest = (match desc with
   | CVals _ | CDone _ -> rest
   | CAnd (t1, t2) | CPar (t1, t2) | CParOr (t1, t2) ->
     let rest = maybe_resume t1 t rest in
     maybe_resume t2 t rest
   | CSame t1 -> maybe_resume t1 t rest
  ) in
  t, rest

let mkcthread t1 t2 varmap rest =
  match Hashtbl.find_opt cthreads_memo (t1.vid, t2.vid) with
  | None ->
    let t, rest = mkcthread_desc (CVals { t1; t2; varmap; cchild = None }) rest in
    Hashtbl.add cthreads_memo (t1.vid, t2.vid) t;
    t, rest
  | Some t -> t, rest

let set_to t desc rest =
  (match t.desc with | CVals _ -> () | _ -> assert false);
  t.desc <- desc;
  let rest = (match desc with
   | CVals _ | CDone _ -> rest
   | CAnd (t1, t2) | CPar (t1, t2) | CParOr (t1, t2) ->
     let rest = maybe_resume t1 t rest in
     maybe_resume t2 t rest
   | CSame t1 -> maybe_resume t1 t rest
  ) in
  check_exit t;
  rest

let rec mk_and_group l rest =
  match l with
  | [] -> mkcthread_desc (CDone true) rest
  | [(t1, t2, varmap)] ->
    mkcthread t1 t2 varmap rest
  | (t1, t2, varmap) :: l ->
    let t, rest = mkcthread t1 t2 varmap rest in
    let nt, rest = mk_and_group l rest in
    mkcthread_desc (CAnd (t, nt)) rest

let set_to_and_group t l rest =
  let nt, rest = mk_and_group l rest in
  set_to t (CSame nt) rest


let freevar x = mkvalptr (Neutral (x, KId, None))

let rec compose_cont k1 k2 =
  match k1 with
  | KId -> k2
  | KApp (v, k) -> KApp (v, compose_cont k k2)
  | KSwitch (branches, env, nbranches, k) -> KSwitch (branches, env, nbranches, compose_cont k k2)
  | KFix (name, body, env, v, k) -> KFix (name, body, env, v, compose_cont k k2)

let rec compare_cont_exn varmap k1 k2 =
  match k1, k2 with
  | KId, KId -> []
  | KApp (u1, k1), KApp (u2, k2) ->
    (u1, u2, varmap) :: (compare_cont_exn varmap k1 k2)
  | KSwitch (_, _, branches1, k1), KSwitch (_, _, branches2, k2) ->
    let l = compare_cont_exn varmap k1 k2 in
    if List.length branches1 <> List.length branches2 then raise Exit;
    let nl = List.map2 (fun (xs1, u1) (xs2, u2) ->
        if List.length xs1 <> List.length xs2 then raise Exit;
        (u1, u2, List.fold_left2 (fun vm x1 x2 -> SMap.add x1 x2 vm) varmap xs1 xs2)
      ) branches1 branches2 in
    nl @ l
  | KFix (_, _, _, v1, k1), KFix (_, _, _, v2, k2) ->
    (v1, v2, varmap) :: compare_cont_exn varmap k1 k2
  | _ -> raise Exit

let compare_cont varmap k1 k2 =
  try Some (compare_cont_exn varmap k1 k2) with Exit -> None

let rec run_threads csts ts =
  if count then incr steps;
  (* Format.printf "%d@." (List.length (fst ts) + List.length (snd ts)); *)
  if debug then begin
    Format.printf "ts = %a@." (pp_list pp_threadid) (List.append (fst ts) (List.rev (snd ts)));
    print_all ();
    Format.printf "@.==================@."
  end;
  match pop_front ts with
  | None -> ()
  | Some (Reduce ({ code; env; cont; self; nblocking; blocking } as t), rest) ->
    (* Format.eprintf "REDUCE: %a@." pp_rthread t; *)
    begin
      run_threads csts @@ if nblocking = 0 then rest else match code with
        | Term (App (u, v)) ->
          t.code <- Term u;
          t.cont <- KApp (makelazy v env, cont);
          push_front rest (Reduce t)
        | Term (Lam (x, u)) ->
          begin match cont with
            | KId ->
              let y = fresh x in
              exit_thread t (Clos (x, u, env, y, makelazy u (SMap.add x (freevar y) env))) rest
            | KApp (v, cont) ->
              t.code <- Term u;
              t.env <- SMap.add x v env;
              t.cont <- cont;
              push_back rest (Reduce t)
            | KSwitch _ | KFix _ -> assert false (* switch on lambda *)
          end
        | Term (Constr (tag, l)) ->
          begin match cont with
            | KId ->
              exit_thread t (Block (tag, List.map (fun u -> makelazy u env) l)) rest
            | KApp _ -> assert false (* app on constructor *)
            | KSwitch (branches, nenv, _, cont) ->
              let (xs, u) = List.nth branches tag in
              assert (List.length xs = List.length l);
              t.code <- Term u;
              t.env <- List.fold_left2 (fun nenv2 x u -> SMap.add x (makelazy u env) nenv2) env xs l;
              t.cont <- cont;
              push_back rest (Reduce t)
            | KFix (x, body, env, _, cont) ->
              t.code <- Val (mkvalptr (Block (tag, List.map (fun u -> makelazy u env) l)));
              push_front rest (Reduce t)
          end
        | Term (Switch (u, branches)) ->
          let nbranch (xs, v) =
            let ys = List.map fresh xs in
            (ys, makelazy u (List.fold_left2 (fun nenv x y -> SMap.add x (freevar y) nenv) env xs ys))
          in
          t.code <- Term u;
          t.cont <- KSwitch (branches, env, List.map nbranch branches, cont);
          push_front rest (Reduce t)
        | Term (Fix (f, args, body)) ->
          let nf = fresh f in
          let nargs = List.map fresh args in
          let nenv = List.fold_left2 (fun nenv x y -> SMap.add x (freevar y) nenv) env (f :: args) (nf :: nargs) in
          let vptr = mkvalptr dummy_value in
          vptr.value <- Fixpoint (args, body, SMap.add f vptr env, nf, nargs, makelazy body nenv, []);
          t.code <- Val vptr; push_front rest (Reduce t)
        | Term (Var x) ->
          let a = SMap.find x env in
          t.code <- Val a;
          push_front rest (Reduce t)
        | Val a ->
          match a.value with
          (* | Lazy (u, e) -> wait_for (Reduce t) (start_lazy a u e) rest *)
          | Thread nt -> wait_for (Reduce t) nt rest
          | Neutral (head, ncont, nf) ->
            let nnf = match nf with
              | None -> None
              | Some (b, p) ->
                let rec rt = { code = Val b; env; cont; self = { value = Thread rt ; vid = freshid () } ; blocking = []; nblocking = 0; rchild = None; rid = freshid () ; dead = false } in
                let () = register_rthread rt in (* for debug *)
                Some (rt.self, p)
            in
            exit_thread t (Neutral (head, compose_cont ncont cont, nnf)) rest
          | Clos (y, u, e, z, nf) ->
            begin match cont with
              | KId ->
                exit_thread t a.value rest
              | KApp (v, cont) ->
                t.code <- Term u;
                t.env <- SMap.add y v e;
                t.cont <- cont;
                push_back rest (Reduce t)
              | KSwitch _ | KFix _ -> assert false (* switch on lambda *)
            end
          | Block (tag, l) ->
            begin match cont with
              | KId ->
                exit_thread t a.value rest
              | KApp _ -> assert false (* app on constructor *)
              | KSwitch (branches, nenv, _, cont) ->
                let (xs, u) = List.nth branches tag in
                assert (List.length xs = List.length l);
                t.code <- Term u;
                t.env <- List.fold_left2 (fun nenv2 x v -> SMap.add x v nenv2) env xs l;
                t.cont <- cont;
                push_back rest (Reduce t)
              | KFix (x, body, env, _, cont) ->
                t.code <- Term body;
                t.env <- SMap.add x a env;
                t.cont <- cont;
                push_back rest (Reduce t)
            end
          | Fixpoint (args, body, env, f, nargs, nf, l) ->
            begin match cont with
              | KId -> exit_thread t a.value rest
              | KSwitch _ | KFix _ -> assert false (* switch on fix *)
              | KApp (v, cont) ->
                begin match args with
                  | [] -> assert false
                  | [x] ->
                    (* Reached the forced argument *)
                    t.code <- Val v;
                    t.cont <- KFix (x, body, env, a, cont);
                    push_back rest (Reduce t)
                  | x :: args ->
                    t.code <- Val (mkvalptr (Fixpoint (args, body, SMap.add x v env, f, nargs, nf, v :: l)));
                    t.cont <- cont;
                    push_back rest (Reduce t)
                end
            end
    end
  | Some (Convert ({ running; desc = CVals { t1; t2; varmap }} as t), rest) ->
    (* Format.eprintf "CONVERT: %a@." pp_cthread t; *)
    begin
      run_threads csts @@ if not running then rest else match t1.value, t2.value with
        (* If one term is being reduced, wait for it *)
        | Thread nt, _ | _, Thread nt -> wait_for (Convert t) nt rest

        (* Comparing \x.u with \y.v: compare u and v, note that x and y are the same variable *)
        | Clos (x1, u1, e1, y1, nf1), Clos (x2, u2, e2, y2, nf2) ->
          let nt, rest = mkcthread nf1 nf2 (SMap.add y1 y2 varmap) rest in
          set_to t (CSame nt) rest

        (* Comparing two blocks *)
        | Block (tag1, l1), Block (tag2, l2) ->
          if tag1 = tag2 && List.length l1 = List.length l2 then
            set_to_and_group t (List.map2 (fun u1 u2 -> (u1, u2, varmap)) l1 l2) rest
          else
            (exit_cthread t false; rest)

        | Fixpoint (_, _, _, f1, args1, nf1, l1), Fixpoint (_, _, _, f2, args2, nf2, l2) ->
          if List.length args1 = List.length args2 && List.length l1 = List.length l2 then
            let l = List.map2 (fun u1 u2 -> (u1, u2, varmap)) l1 l2 in
            let bodymap = List.fold_left2 (fun vm x1 x2 -> SMap.add x1 x2 vm) varmap (f1 :: args1) (f2 :: args2) in
            set_to_and_group t ((nf1, nf2, bodymap) :: l) rest
          else
            (exit_cthread t false; rest)

        | Clos _, Block _ | Block _, Clos _ | Fixpoint _, Block _ | Block _, Fixpoint _
          (* Naively, the cases above are type errors. However, it could happen if both terms are not of the same type because
             we made an incorrect hypothesis earlier, for instance:

             app f x = f x
             app (fun _ -> C) (fun x -> x) =? app (fun _ -> C) C
          *)
        | Clos _, Fixpoint _ | Fixpoint _, Clos _ ->
          exit_cthread t false; rest

        | Neutral (hd1, cont1, nf1), Neutral (hd2, cont2, nf2) ->
          (* Format.eprintf "%s %s %a %a@." hd1 hd2 (pp_cont (fun ff -> Format.fprintf ff "[]")) cont1 (pp_cont (fun ff -> Format.fprintf ff "[]")) cont2; *)
          let hda = try SMap.find hd1 varmap with Not_found -> hd1 in
          let compared_conts =
            if hda <> hd2 then
              None
            else
              compare_cont varmap cont1 cont2
          in
          begin match nf1, nf2 with
            | Some (nf1, _), Some (nf2, _) ->
              let nt1, rest = mkcthread t1 nf2 varmap rest in
              let nt2, rest = mkcthread nf1 t2 varmap rest in
              (match compared_conts with
               | None ->
                 set_to t (CPar (nt1, nt2)) rest
               | Some l ->
                 let nt, rest = mk_and_group l rest in
                 let cp, rest = mkcthread_desc (CPar (nt1, nt2)) rest in
                 set_to t (CParOr (cp, nt)) rest
              )
            | Some (nf1, _), None ->
              let nt, rest = mkcthread nf1 t2 varmap rest in
              set_to t (CSame nt) rest
            | None, Some (nf2, _) ->
              let nt, rest = mkcthread t1 nf2 varmap rest in
              set_to t (CSame nt) rest
            | None, None ->
              match compared_conts with
              | None -> exit_cthread t false; rest
              | Some l ->
                set_to_and_group t l rest
          end
        | Neutral (hd1, stk1, nf1), (Clos _ | Block _ | Fixpoint _) ->
          (match nf1 with
           | None -> exit_cthread t false; rest
           | Some (nf1, _) -> let nt, rest = mkcthread nf1 t2 varmap rest in set_to t (CSame nt) rest)
        | (Clos _ | Block _ | Fixpoint _), Neutral (hd2, stk2, nf2) ->
          (match nf2 with
           | None -> exit_cthread t false; rest
           | Some (nf2, _) -> let nt, rest = mkcthread t1 nf2 varmap rest in set_to t (CSame nt) rest)
    end
  | Some (Convert { desc = _; _}, rest) -> run_threads csts rest

let check_conv csts t1 t2 =
  let base_env = List.fold_left (fun env (name, p, body) ->
      SMap.add name (mkvalptr (Neutral (name, KId, Some (makelazy body env, p)))) env
    ) SMap.empty csts in
  let init_thread, init_state = mkcthread (makelazy t1 base_env) (makelazy t2 base_env) SMap.empty empty_queue in
  init_thread.running_parents <- 1;
  let init_state = resume_cthread init_thread init_state in
  run_threads csts init_state;
  match init_thread.desc with
  | CDone b -> b
  | _ -> assert false


let church n =
  let rec loop n =
    if n = 0 then Var "x" else App (Var "f", loop (n - 1))
  in
  Lam ("f", Lam ("x", loop n))

let rec peano n =
  if n = 0 then Constr (0, []) else Constr (1, [peano (n - 1)])

let app f x = App (Var f, x)
let app2 f x y = App (App (Var f, x), y)

let csts = [
  ("add", 0, Lam ("n", Lam ("m", Lam ("f", Lam ("x", App (App (Var "n", Var "f"), App (App (Var "m", Var "f"), Var "x")))))));
  ("mul", 0, Lam ("n", Lam ("m", Lam ("f", Lam ("x", App (App (Var "n", App (Var "m", Var "f")), Var "x"))))));
  ("pow", 0, Lam ("n", Lam ("m", App (Var "m", Var "n"))));
  ("exp2", 0, Lam ("n", App (Var "n", church 2)));
  ("F", 0, Lam ("x", Lam ("y", Var "y")));
  ("W", 0, Lam ("x", App (Var "exp2", church 20)));
  ("true", 0, Lam ("x", Lam ("y", Var "x")));
  ("false", 0, Lam ("x", Lam ("y", Var "y")));
  ("iszero", 0, Lam ("n", app2 "n" (Lam ("u", Var "false")) (Var "true")));

  ("addP", 0, Fix ("rec", ["n"], Lam ("m", Switch (Var "n", [[], Var "m"; ["n2"], Constr(1, [app2 "rec" (Var "n2") (Var "m")])]))));
  ("mulP", 0, Fix ("rec", ["n"], Lam ("m", Switch (Var "n", [[], Constr (0, []); ["n2"], app2 "addP" (Var "m") (app2 "rec" (Var "n2") (Var "m"))]))));
  ("exp2P", 0, Fix ("rec", ["n"], Switch (Var "n", [[], peano 1; ["n2"], app2 "mulP" (peano 2) (app "rec" (Var "n2"))])));
  ("is_zeroP", 0, Lam("n", Switch (Var "n", [[], Constr (1, []); ["n2"], Constr (0, [])])));
  ("test7pair", 0, Lam("n", Constr (0, [app "is_zeroP" (Var "n"); Var "n"])));
  ("test8pair", 0, Lam("n", Constr (0, [Var "n"; app "is_zeroP" (Var "n")])));

  ("explode_share", 0, Fix ("rec", ["n"], Lam ("t", Switch (Var "n", [[], Var "t"; ["n2"], app2 "rec" (Var "n2") (Constr (1, [Var "t"; Var "t"]))]))));
  ("left_depth", 0, Fix ("rec", ["t"], Switch (Var "t", [[], Constr (0, []); ["t1"; "t2"], Constr(1, [app "rec" (Var "t1")])])));
  ("left_depth2", 0, Fix ("rec", ["t"], Switch (Var "t", [[], Constr (0, []); ["t1"; "t2"], app2 "addP" (app "rec" (Var "t1")) (Constr (1, [Constr (0, [])]))])));
]

let[@inline never] running_time f =
  Hashtbl.clear cthreads_memo;
  Gc.full_major ();
  let start = Unix.gettimeofday () in
  match f () with
  | r -> let stop = Unix.gettimeofday () in Format.eprintf "Took %fs@." (stop -. start); r
  | exception e -> let stop = Unix.gettimeofday () in Format.eprintf "Took %fs@." (stop -. start); raise e


let test_check_conv ?(name = "") ?(csts = csts) t1 t2 =
  Format.eprintf "====== %s@." name;
  Format.eprintf "t1 = %a@." pp_term t1;
  Format.eprintf "t2 = %a@." pp_term t2;
  steps := 0;
  let r = running_time (fun () -> check_conv csts t1 t2) in
  if !steps > 0 then
    Format.eprintf "Steps: %d@." !steps;
  r

(*
let () = assert (test_check_conv (Lam ("x", Var "x")) (Lam ("x", Var "x")))
let () = assert (test_check_conv (church 1) (church 1))
let () = assert (test_check_conv (App (Var "exp2", church 15)) (App (Var "exp2", App (App (Var "add", church 14), church 1))))
(* let () = assert (test_check_conv (App (Var "W", church 10)) (App (Var "W", App (App (Var "add", church 4), church 7)))) *)
let () = assert (test_check_conv (App (Var "F", App (Var "exp2", church 29))) (App (Var "F", App (Var "exp2", church 30))))
let () = assert (not (test_check_conv (App (Var "exp2", church 10)) (App (Var "exp2", church 30))))
let () = assert (not (test_check_conv (App (Var "exp2", church 30)) (App (Var "exp2", church 10))))
(* let () = assert (test_check_conv (App (App (Var "pow", church 2), church 22)) (App (App (Var "mul", church 2048), church 2048))) *)
let () = assert (test_check_conv (Lam ("x", app2 "mul" (church 2) (Var "x"))) (Lam ("x", app2 "add" (Var "x") (Var "x"))))
let () = assert (test_check_conv (app "iszero" (app "exp2" (church 30))) (Var "false"))

let () = assert (test_check_conv (app2 "addP" (peano 12) (peano 5)) (peano 17))
let () = assert (not (test_check_conv (app2 "addP" (peano 12) (peano 5)) (peano 18)))
let () = assert (test_check_conv (app2 "mulP" (peano 12) (peano 5)) (peano 60))

let () = assert (test_check_conv (App (Var "exp2P", peano 30)) (App (Var "exp2P", App (App (Var "addP", peano 10), peano 20))))
let () = assert (test_check_conv (App (Var "F", App (Var "exp2P", peano 29))) (App (Var "F", App (Var "exp2P", peano 30))))
let () = assert (not (test_check_conv (App (Var "exp2P", peano 10)) (App (Var "exp2P", peano 30))))
let () = assert (not (test_check_conv (App (Var "exp2P", peano 30)) (App (Var "exp2P", peano 10))))

let () = assert (test_check_conv (Lam ("x", app2 "mul" (church 2) (app2 "add" (church 100) (Var "x")))) (Lam ("x", app2 "add" (church 100) (app2 "add" (Var "x") (app2 "add" (church 100) (Var "x"))))))

let () = assert (test_check_conv
  (app "left_depth" (app2 "explode_share" (peano 15) (Constr (0, []))))
  (app "left_depth2" (app2 "explode_share" (peano 15) (Constr (0, []))))
)
let () = assert (test_check_conv
  (app "left_depth" (app2 "explode_share" (peano 15) (Constr (0, []))))
  (app "left_depth" (app2 "explode_share" (peano 14) (Constr (1, [Constr (0, []); Constr (0, [])]))))
)

let () = assert (not (test_check_conv
  (Constr (0, [Constr(0, []); app "exp2P" (peano 30)]))
  (Constr (0, [Constr(1, []); app "exp2P" (peano 29)]))
))

let () = assert (not (test_check_conv
  (Constr (0, [app "exp2P" (peano 30); Constr(0, [])]))
  (Constr (0, [app "exp2P" (peano 29); Constr(1, [])]))
))
*)

let () = assert (test_check_conv ~name:"test1" (App (Var "exp2P", peano 15)) (App (Var "exp2P", App (App (Var "addP", peano 14), peano 1))))
let () = assert (test_check_conv ~name:"test1c" (App (Var "exp2", church 15)) (App (Var "exp2", App (App (Var "add", church 14), church 1))))
let () = assert (test_check_conv ~name:"test2" (App (Var "F", App (Var "exp2P", peano 15))) (App (Var "F", App (Var "exp2P", peano 16))))
let () = assert (test_check_conv ~name:"test3"
  (app "left_depth" (app2 "explode_share" (peano 15) (Constr (0, []))))
  (app "left_depth2" (app2 "explode_share" (peano 15) (Constr (0, []))))
)
let () = assert (test_check_conv ~name:"test4"
  (app2 "explode_share" (peano 15) (Constr (0, [])))
  (app2 "explode_share" (peano 14) (Constr (1, [Constr (0, []); Constr (0, [])])))
)

let () = assert (not (test_check_conv ~name:"test5"
  (Constr (0, [app "exp2P" (peano 15); Constr(0, [])]))
  (Constr (0, [app "exp2P" (peano 16); Constr(1, [])]))
))
let () = assert (not (test_check_conv ~name:"test6"
  (Constr (0, [Constr(0, []); app "exp2P" (peano 15)]))
  (Constr (0, [Constr(1, []); app "exp2P" (peano 16)]))
))
let () = assert (test_check_conv ~name:"test7"
  (app "test7pair" (app "exp2P" (peano 15)))
  (Constr (0, [Constr(0, []); app "exp2P" (peano 15)]))
)
let () = assert (test_check_conv ~name:"test8"
  (app "test8pair" (app "exp2P" (peano 15)))
  (Constr (0, [app "exp2P" (peano 15); Constr(0, [])]))
)

let () =
  (* let appid t = App (Lam ("z", Var "z"), t) in *)
  let rec napps f x n =
    if n = 0 then x
    else App (f, napps f x (n - 1))
  in
  let go name order =
    assert (test_check_conv ~name ~csts:([
        "f0", order 0, Lam ("n", Var "n");
        "f1", order 1, Lam ("n", napps (Var "f0") (Var "n") 2);
        "f2", order 2, Lam ("n", napps (Var "f1") (Var "n") 2);
        "f3", order 3, Lam ("n", napps (Var "f2") (Var "n") 2);
        "f4", order 4, Lam ("n", napps (Var "f3") (Var "n") 2);
      ])
      (napps (Var "f4") (Constr (0, [])) 30)
      (napps (Var "f4") (Constr (0, [])) 30)
    )
  in
  go "test9a" (fun x -> x);
  go "test9b" (fun x -> -x)


(*
let test1 n =
  let rec napps f x n =
    if n = 0 then x
    else App (f, napps f x (n - 1))
  in
  let rec aux k =
    if k = 0 then
      ["f", k, Lam ("x", Var "x")], "f"
    else
      let csts, f1 = aux (k - 1) in
      let f = fresh "f" in
      (f, k, Lam ("x", napps (Var f1) (Var "x") 2)) :: csts, f
  in
  let csts, f = aux n in
  let csts = List.rev csts in
  assert ( (check_conv csts (napps (Var f) (Lam ("x", Lam ("y", Var "x"))) n) (napps (Var f) (Lam ("x", Lam ("y", Var "x"))) 1)))

let () = Format.printf "Start@."
let () = running_time (fun () -> test1 8)
let () = Format.printf "8 ok@."
*)

(*
let () = test1 100
let () = Format.printf "100 ok@."
*)

(* let () = assert (not (check_conv csts (App (Var "exp2", church 22)) (App (Var "exp2", church 23)))) *)
(* let () = assert (not (check_conv csts (App (Var "exp2", church 30)) (App (Var "exp2", App (App (Var "add", church 10), church 21))))) *)
(* let () = assert (not (check_conv csts (App (Var "exp2", church 1)) (App (Var "exp2", App (App (Var "add", church 1), church 1)))) *)
