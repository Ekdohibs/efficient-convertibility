
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
    | Var s -> Format.fprintf ff "%s" s
    | Lam (x, t) -> Format.fprintf ff "(\\%a.%a)" print x print t
    | App (t1, t2) -> Format.fprintf ff "(%a %a)" print t1 print t2


let result = (getnf ((fun df n3 -> (mklam (fun df f2 -> (mklam (fun df x1 -> ((fst ((fst (lazy_force n3 false)) false f2)) df (mklazy (fun df -> ((fst (lazy_force f2 false)) df x1))))) "x1" df)) "f2" df)) true (mkval ((fun df f24 -> (mklam (fun df x23 -> ((fst (lazy_force f24 false)) df (mklazy (fun df -> ((fst (lazy_force f24 false)) df (mklazy (fun df -> ((fst (lazy_force f24 false)) df (mklazy (fun df -> ((fst (lazy_force f24 false)) df x23))))))))))) "x23" df)), ref (Prevar "f24"))))) let () = Format.printf "%a@." print result
let result = (getnf ((fst ((fun df m12 -> (mklam (fun df n11 -> ((fst (lazy_force n11 false)) df m12)) "n11" df)) false (mkval ((fun df f28 -> (mklam (fun df x27 -> ((fst (lazy_force f28 false)) df (mklazy (fun df -> ((fst (lazy_force f28 false)) df (mklazy (fun df -> ((fst (lazy_force f28 false)) df (mklazy (fun df -> ((fst (lazy_force f28 false)) df (mklazy (fun df -> ((fst (lazy_force f28 false)) df (mklazy (fun df -> ((fst (lazy_force f28 false)) df (mklazy (fun df -> ((fst (lazy_force f28 false)) df (mklazy (fun df -> ((fst (lazy_force f28 false)) df (mklazy (fun df -> ((fst (lazy_force f28 false)) df (mklazy (fun df -> ((fst (lazy_force f28 false)) df x27))))))))))))))))))))))))))))) "x27" df)), ref (Prevar "f28"))))) true (mkval ((fun df f26 -> (mklam (fun df x25 -> ((fst (lazy_force f26 false)) df (mklazy (fun df -> ((fst (lazy_force f26 false)) df x25))))) "x25" df)), ref (Prevar "f26"))))) let () = Format.printf "%a@." print result
let result = (getnf ((fun df n -> ((fst ((fst (lazy_force n false)) false (mkval ((fun df b -> (mklam (fun df x -> (mklam (fun df y -> ((fst ((fst (lazy_force b false)) false y)) df x)) "y" df)) "x" df)), ref (Prevar "b"))))) df (mkval ((fun df x -> (mklam (fun df y -> (lazy_force x df)) "y" df)), ref (Prevar "x"))))) true (mklazy (fun df -> ((fst ((fun df m12 -> (mklam (fun df n11 -> ((fst (lazy_force n11 false)) df m12)) "n11" df)) false (mkval ((fun df f32 -> (mklam (fun df x31 -> ((fst (lazy_force f32 false)) df (mklazy (fun df -> ((fst (lazy_force f32 false)) df (mklazy (fun df -> ((fst (lazy_force f32 false)) df (mklazy (fun df -> ((fst (lazy_force f32 false)) df (mklazy (fun df -> ((fst (lazy_force f32 false)) df (mklazy (fun df -> ((fst (lazy_force f32 false)) df (mklazy (fun df -> ((fst (lazy_force f32 false)) df (mklazy (fun df -> ((fst (lazy_force f32 false)) df (mklazy (fun df -> ((fst (lazy_force f32 false)) df (mklazy (fun df -> ((fst (lazy_force f32 false)) df x31))))))))))))))))))))))))))))) "x31" df)), ref (Prevar "f32"))))) df (mkval ((fun df f30 -> (mklam (fun df x29 -> ((fst (lazy_force f30 false)) df (mklazy (fun df -> ((fst (lazy_force f30 false)) df (mklazy (fun df -> ((fst (lazy_force f30 false)) df (mklazy (fun df -> ((fst (lazy_force f30 false)) df (mklazy (fun df -> ((fst (lazy_force f30 false)) df (mklazy (fun df -> ((fst (lazy_force f30 false)) df (mklazy (fun df -> ((fst (lazy_force f30 false)) df (mklazy (fun df -> ((fst (lazy_force f30 false)) df x29))))))))))))))))))))))) "x29" df)), ref (Prevar "f30")))))))) let () = Format.printf "%a@." print result
let result = (getnf ((fst ((fun df m12 -> (mklam (fun df n11 -> ((fst (lazy_force n11 false)) df m12)) "n11" df)) false (mkval ((fun df f36 -> (mklam (fun df x35 -> ((fst (lazy_force f36 false)) df (mklazy (fun df -> ((fst (lazy_force f36 false)) df (mklazy (fun df -> ((fst (lazy_force f36 false)) df (mklazy (fun df -> ((fst (lazy_force f36 false)) df (mklazy (fun df -> ((fst (lazy_force f36 false)) df (mklazy (fun df -> ((fst (lazy_force f36 false)) df (mklazy (fun df -> ((fst (lazy_force f36 false)) df (mklazy (fun df -> ((fst (lazy_force f36 false)) df (mklazy (fun df -> ((fst (lazy_force f36 false)) df (mklazy (fun df -> ((fst (lazy_force f36 false)) df x35))))))))))))))))))))))))))))) "x35" df)), ref (Prevar "f36"))))) true (mkval ((fun df f34 -> (mklam (fun df x33 -> ((fst (lazy_force f34 false)) df (mklazy (fun df -> ((fst (lazy_force f34 false)) df (mklazy (fun df -> ((fst (lazy_force f34 false)) df (mklazy (fun df -> ((fst (lazy_force f34 false)) df (mklazy (fun df -> ((fst (lazy_force f34 false)) df x33)))))))))))))) "x33" df)), ref (Prevar "f34")))))