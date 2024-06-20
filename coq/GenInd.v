From Ltac2 Require Import Ltac2.

Require Import List.
Require Import Rewrite.
Require Import Misc.

Ltac2 eassumption_tac () := ltac1:(eassumption).
Ltac2 Notation eassumption := eassumption_tac ().

Definition proj1_transparent {A B : Prop} (H : A /\ B) : A := match H with conj P Q => P end.
Definition proj2_transparent {A B : Prop} (H : A /\ B) : B := match H with conj P Q => Q end.

Lemma Exists_impl_transparent :
  forall (A : Type) (P Q : A -> Prop) (L : list A), (forall x, P x -> Q x) -> Exists P L -> Exists Q L.
Proof.
  intros A P Q L H1 H2. induction H2.
  - apply Exists_cons_hd, H1. assumption.
  - apply Exists_cons_tl, IHExists.
Defined.

Lemma Exists_impl_strong_transparent :
  forall (A : Type) (P Q : A -> Prop) (L : list A), (forall x, P x -> Q x) -> Exists P L -> Exists (fun x => P x /\ Q x) L.
Proof.
  intros A P Q L H1 H2. eapply Exists_impl_transparent > [|eassumption].
  intros x Hx; split > [apply Hx|apply H1, Hx].
Defined.

Lemma Forall3_impl_transparent :
  forall (A B C : Type) (P Q : A -> B -> C -> Prop) (l1 : list A) (l2 : list B) (l3 : list C), (forall x y z, P x y z -> Q x y z) -> Forall3 P l1 l2 l3 -> Forall3 Q l1 l2 l3.
Proof.
  intros A B C P Q l1 l2 l3 H1 H2; induction H2; constructor.
  - apply H1. assumption.
  - assumption.
Defined.

Inductive if_Some {A : Type} (P : A -> Prop) : option A -> Prop :=
| if_Some_None : if_Some P None
| if_Some_Some : forall x, P x -> if_Some P (Some x).

Lemma if_Some_impl_transparent :
  forall (A : Type) (P Q : A -> Prop) (x : option A), (forall x, P x -> Q x) -> if_Some P x -> if_Some Q x.
Proof.
  intros A P Q x H1 H2. inversion H2; subst.
  - constructor.
  - constructor; apply H1. assumption.
Defined.

Inductive if_Some2 {A B : Type} (P : A -> B -> Prop) : option A -> option B -> Prop :=
| if_Some2_None : if_Some2 P None None
| if_Some2_Some : forall x y, P x y -> if_Some2 P (Some x) (Some y).

Lemma if_Some2_impl_transparent :
  forall (A B : Type) (P Q : A -> B -> Prop) (x : option A) (y : option B), (forall x y, P x y -> Q x y) -> if_Some2 P x y -> if_Some2 Q x y.
Proof.
  intros A B P Q x y H1 H2. inversion H2; subst.
  - constructor.
  - constructor; apply H1. assumption.
Defined.

Inductive if_Some3 {A B C : Type} (P : A -> B -> C -> Prop) : option A -> option B -> option C -> Prop :=
| if_Some3_None : if_Some3 P None None None
| if_Some3_Some : forall x y z, P x y z -> if_Some3 P (Some x) (Some y) (Some z).

Lemma if_Some3_impl_transparent :
  forall (A B C : Type) (P Q : A -> B -> C -> Prop) (x : option A) (y : option B) (z : option C), (forall x y z, P x y z -> Q x y z) -> if_Some3 P x y z -> if_Some3 Q x y z.
Proof.
  intros A B C P Q x y z H1 H2. inversion H2; subst.
  - constructor.
  - constructor; apply H1. assumption.
Defined.


(*
Lemma exists_impl_transparent :
  forall (A : Type) (P Q : A -> Prop), (exists x, P x) -> (forall x, P x -> Q x) -> (exists x, Q x).
Proof.
  intros A P Q [x H1] H2. exists x. apply H2, H1.
Defined.

Lemma exists_impl_strong_transparent :
  forall (A : Type) (P Q : A -> Prop), (exists x, P x) -> (forall x, P x -> Q x) -> (exists x, P x /\ Q x).
Proof.
  intros A P Q H1 H2. eapply exists_impl_transparent > [eassumption|].
  intros x Hx; split > [apply Hx|apply H2, Hx].
Defined.
*)

Ltac2 msg_list_concat (l : message list) (sep : message) :=
  match l with
  | [] => Message.of_string ""
  | x :: l => List.fold_left (fun m x => Message.concat m (Message.concat sep x)) l x
  end.

Ltac2 message_concat_list (l : message list) :=
  List.fold_left (fun m1 m2 => Message.concat m1 m2) l (Message.of_string "").

Ltac2 message_of_hyps () :=
  message_concat_list (List.map (fun (id, _, c) => message_concat_list [Message.of_ident id; Message.of_string " : "; Message.of_constr c; Message.of_string "
"]) (Control.hyps ())).

Ltac2 typed_constr_message (c : constr) :=
  Message.concat (Message.concat (Message.of_constr c) (Message.of_string " : ")) (Message.of_constr (Constr.type c)).

Ltac2 msg_of_binder (b : binder) :=
  Message.concat
    (match Constr.Binder.name b with None => Message.of_string "_" | Some x => Message.of_ident x end)
    (Message.concat (Message.of_string " : ")
                    (typed_constr_message (Constr.Binder.type b))).

Ltac2 msg_of_list (l : message list) :=
  message_concat_list [Message.of_string "[" ; msg_list_concat l (Message.of_string "; "); Message.of_string "]"].

Ltac2 msg_of_array (a : message array) :=
  message_concat_list [Message.of_string "[|" ; msg_list_concat (Array.to_list a) (Message.of_string "; "); Message.of_string "|]"].

Ltac2 show_constr_kind (c : constr) :=
  let sp := Message.of_string " " in
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.Rel n => Message.concat (Message.of_string "Rel ") (Message.of_int n)
  | Constr.Unsafe.Var x => Message.concat (Message.of_string "Var ") (Message.of_ident x)
  | Constr.Unsafe.Meta _ => Message.of_string "Meta _"
  | Constr.Unsafe.Evar e ca => Message.concat (Message.of_string "Evar _ ") (msg_of_array (Array.map Message.of_constr ca))
  | Constr.Unsafe.Sort _ => Message.of_string "Sort _"
  | Constr.Unsafe.Cast c1 _ c2 => message_concat_list [Message.of_string "Cast " ; Message.of_constr c1 ; Message.of_string " _ " ; Message.of_constr c2]
  | Constr.Unsafe.Prod b c => message_concat_list [Message.of_string "Prod " ; msg_of_binder b ; sp ; Message.of_constr c]
  | Constr.Unsafe.Lambda  b c => message_concat_list [Message.of_string "Lambda " ; msg_of_binder b ; sp ; Message.of_constr c]
  | Constr.Unsafe.LetIn b c1 c2 => message_concat_list [Message.of_string "LetIn " ; msg_of_binder b ; sp ; Message.of_constr c1 ; sp ; Message.of_constr c2]
  | Constr.Unsafe.App c ca => message_concat_list [Message.of_string "App " ; Message.of_constr c ; sp; msg_of_array (Array.map Message.of_constr ca)]
  | Constr.Unsafe.Constant _ _ => Message.of_string "Constant _ _"
  | Constr.Unsafe.Ind _ _ => Message.of_string "Ind _ _"
  | Constr.Unsafe.Constructor _ _ => Message.of_string "Constructor _ _"
  | Constr.Unsafe.Case _ c1 ci c2 ca => message_concat_list [Message.of_string "Case _ " ; Message.of_constr c1 ; sp ; match ci with Constr.Unsafe.NoInvert => Message.of_string "NoInvert" | Constr.Unsafe.CaseInvert ca => message_concat_list [Message.of_string "(CaseInvert "; msg_of_array (Array.map Message.of_constr ca); Message.of_string ")"] end ; sp ; Message.of_constr c2 ; sp ; msg_of_array (Array.map Message.of_constr ca) ]
  | Constr.Unsafe.Fix ia i ba ca => message_concat_list [Message.of_string "Fix "; msg_of_array (Array.map Message.of_int ia); sp ; Message.of_int i ; sp ; msg_of_array (Array.map msg_of_binder ba) ; sp ; msg_of_array (Array.map Message.of_constr ca)]
  | Constr.Unsafe.CoFix i ba ca => message_concat_list [Message.of_string "CoFix "; Message.of_int i ; sp ; msg_of_array (Array.map msg_of_binder ba) ; sp ; msg_of_array (Array.map Message.of_constr ca)]
  | Constr.Unsafe.Proj _ c => message_concat_list [Message.of_string "Proj _ "; Message.of_constr c]
  | Constr.Unsafe.Uint63 _ => Message.of_string "Uint63 _"
  | Constr.Unsafe.Float _ => Message.of_string "Float _"
  | Constr.Unsafe.Array _ ca c1 c2 => message_concat_list [Message.of_string "Array _ "; msg_of_array (Array.map Message.of_constr ca) ; sp ; Message.of_constr c1 ; sp ; Message.of_constr c2]
  end.
(*
Inductive even : nat -> Prop :=
| even_O : even O
| even_SS : forall n, even n -> even (S (S n)).
Print even_ind.
(*Fixpoint t (n : nat) (H : even n) : Prop :=
  match H return Prop with
  | even_O => n = n
  | even_SS n H1 => t n H1
  end.*)
Goal True.
  let tdef := Std.eval_cbv {Std.rBeta := true ; Std.rMatch := false ; Std.rFix := false ; Std.rCofix := false ; Std.rZeta := false ; Std.rDelta := true ; Std.rConst := []} '(even_ind (fun n => even n) even_O (fun n _ Hrec => even_SS n Hrec)) in
  Message.print (show_constr_kind tdef).
*)
Ltac2 get_binder_maybe (c : constr) :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.Prod b _ => Some b
  | Constr.Unsafe.Lambda b _ => Some b
  | Constr.Unsafe.LetIn b _ _ => Some b
  | _ => None
  end.

Ltac2 get_binder (c : constr) :=
  match get_binder_maybe c with
  | Some b => b
  | None => Control.throw (Invalid_argument (Some (Message.of_constr c)))
  end.

Ltac2 head_binder_ident (c : constr) :=
  Fresh.in_goal (
      match get_binder_maybe c with
      | None => @_x
      | Some b =>
        match Constr.Binder.name b with
        | None => @_x
        | Some x => x
        end
      end).

Ltac2 rec rebuild_lam (t : constr) :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.Lambda b t1 => Constr.Unsafe.make (Constr.Unsafe.Lambda b (rebuild_lam t1))
  | _ => t
  end.

Ltac2 rec rebuild_prod_cast (t : constr) :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.Prod b t1 => Constr.Unsafe.make (Constr.Unsafe.Prod b (rebuild_prod_cast t1))
  | Constr.Unsafe.Lambda b t1 => Constr.Unsafe.make (Constr.Unsafe.Lambda b (rebuild_prod_cast t1))
  | Constr.Unsafe.Cast t1 _ _ => rebuild_prod_cast t1
  | _ => t
  end.

Ltac2 force_prop (tac : unit -> constr) :=
  '(ltac2:(Control.refine tac) : Prop).
Ltac2 force_prop_t (tac : unit -> constr) :=
  '(ltac2:(Control.refine tac) : _ : Prop).

Ltac2 inctx (name : ident) (t : constr) (body : constr -> constr) :=
  rebuild_lam (Constr.in_context name t (fun () => Control.refine (fun () => body (Control.hyp name)))).
Ltac2 inctx_p (name : ident) (t : constr) (body : constr -> constr) :=
  force_prop_t (fun () => inctx name t body).

Ltac2 make_forall (c : constr) :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.Lambda b t => Constr.Unsafe.make (Constr.Unsafe.Prod b t)
  | _ => Control.throw (Invalid_argument (Some (Message.of_constr c)))
  end.

Ltac2 mk_app (u : constr) (v : constr) := '($u $v).
Ltac2 mk_app2 (u : constr) (v : constr) (w : constr) := '($u $v $w).
Ltac2 mk_app3 (u : constr) (v : constr) (w : constr) (x : constr) := '($u $v $w $x).

Ltac2 mk_forall_proof_smart (x : ident) (u : constr) (v : constr -> constr) :=
  lazy_match! (Std.eval_hnf u) with
  | True => v 'I
  | ?u =>
    let vx := inctx_p x u v in
    lazy_match! (Std.eval_hnf (Constr.type vx)) with
    | (_ -> True) => 'I
    | _ => vx
    end
  end.

Ltac2 mk_Forall_proof_smart (x : ident) (t : constr) (u : constr -> constr) (v : constr) :=
  let ux := inctx_p x t u in
  lazy_match! (Std.eval_hnf (Constr.type ux)) with
  | (_ -> True) => 'I
  | _ => '(Forall_True_transparent $t _ $v $ux)
  end.

Ltac2 mk_and_proof_smart (u : constr) (v : constr) :=
  let ut := Std.eval_hnf (Constr.type u) in
  let vt := Std.eval_hnf (Constr.type v) in
  lazy_match! '($ut /\ $vt) with
  | True /\ _ => v
  | _ /\ True => u
  | _ => '(conj $u $v)
  end.


Ltac2 mk_Forall_impl_smart (t : constr) (p : constr) (l : constr) (u : constr -> constr) (v : constr) :=
  let ux := inctx_p (head_binder_ident p) t (fun xx => inctx (Fresh.in_goal @H) (mk_app p xx) u) in
  lazy_match! (Std.eval_hnf (Constr.type ux)) with
  | (forall x H, True) => 'I
  | _ => '(Forall_impl_transparent $t _ _ $l $ux $v)
  end.

Ltac2 mk_Forall2_impl_smart (t1 : constr) (t2 : constr) (p : constr) (l1 : constr) (l2 : constr) (u : constr -> constr) (v : constr) :=
  let ux := inctx_p (head_binder_ident p) t1 (fun xx =>
    let y := head_binder_ident (Std.eval_hnf (mk_app p xx)) in
    inctx_p y t2 (fun yy =>
      inctx_p (Fresh.in_goal @H) (mk_app (mk_app p xx) yy) u)) in
  lazy_match! (Std.eval_hnf (Constr.type ux)) with
  | (forall x y H, True) => 'I
  | _ => '(Forall2_impl_transparent $t1 $t2 _ _ $l1 $l2 $ux $v)
  end.

Ltac2 mk_Forall3_impl_smart (t1 : constr) (t2 : constr) (t3 : constr) (p : constr) (l1 : constr) (l2 : constr) (l3 : constr) (u : constr -> constr) (v : constr) :=
  let ux := inctx_p (head_binder_ident p) t1 (fun xx =>
    let y := head_binder_ident (Std.eval_hnf (mk_app p xx)) in
    inctx_p y t2 (fun yy =>
      let z := head_binder_ident (Std.eval_hnf (mk_app (mk_app p xx) yy)) in
      inctx_p z t3 (fun zz =>
        inctx_p (Fresh.in_goal @H) (mk_app (mk_app (mk_app p xx) yy) zz) u))) in
  lazy_match! (Std.eval_hnf (Constr.type ux)) with
  | (forall x y z H, True) => 'I
  | _ => '(Forall3_impl_transparent $t1 $t2 $t3 _ _ $l1 $l2 $l3 $ux $v)
  end.

Ltac2 mk_if_Some_impl_smart (t : constr) (p : constr) (o : constr) (u : constr -> constr) (v : constr) :=
  let ux := inctx_p (head_binder_ident p) t (fun xx => inctx (Fresh.in_goal @H) (mk_app p xx) u) in
  lazy_match! (Std.eval_hnf (Constr.type ux)) with
  | (forall x H, True) => 'I
  | _ => '(if_Some_impl_transparent $t _ _ $o $ux $v)
  end.

Ltac2 mk_if_Some2_impl_smart (t1 : constr) (t2 : constr) (p : constr) (o1 : constr) (o2 : constr) (u : constr -> constr) (v : constr) :=
  let ux := inctx_p (head_binder_ident p) t1 (fun xx =>
    let y := head_binder_ident (Std.eval_hnf (mk_app p xx)) in
    inctx_p y t2 (fun yy =>
      inctx_p (Fresh.in_goal @H) (mk_app (mk_app p xx) yy) u)) in
  lazy_match! (Std.eval_hnf (Constr.type ux)) with
  | (forall x y H, True) => 'I
  | _ => '(if_Some2_impl_transparent $t1 $t2 _ _ $o1 $o2 $ux $v)
  end.

Ltac2 mk_if_Some3_impl_smart (t1 : constr) (t2 : constr) (t3 : constr) (p : constr) (o1 : constr) (o2 : constr) (o3 : constr) (u : constr -> constr) (v : constr) :=
  let ux := inctx_p (head_binder_ident p) t1 (fun xx =>
    let y := head_binder_ident (Std.eval_hnf (mk_app p xx)) in
    inctx_p y t2 (fun yy =>
      let z := head_binder_ident (Std.eval_hnf (mk_app (mk_app p xx) yy)) in
      inctx_p z t3 (fun zz =>
        inctx_p (Fresh.in_goal @H) (mk_app (mk_app (mk_app p xx) yy) zz) u))) in
  lazy_match! (Std.eval_hnf (Constr.type ux)) with
  | (forall x y z H, True) => 'I
  | _ => '(if_Some3_impl_transparent $t1 $t2 $t3 _ _ $o1 $o2 $o3 $ux $v)
  end.


Ltac2 mk_step_one_impl_smart (t : constr) (r : constr) (l1 : constr) (l2 : constr) (u : constr -> constr) (v : constr) :=
  let ux := inctx_p (head_binder_ident r) t (fun xx =>
    let y := head_binder_ident (Std.eval_hnf (mk_app r xx)) in
    inctx_p y t (fun yy =>
      inctx_p (Fresh.in_goal @H) (mk_app (mk_app r xx) yy) u)) in
  lazy_match! (Std.eval_hnf (Constr.type ux)) with
  | (forall x y H, True) => 'I
  | _ => '(step_one_impl_strong_transparent $t _ _ $l1 $l2 $ux $v)
  end.

Ltac2 mk_Exists_impl_smart (t : constr) (p : constr) (l : constr) (u : constr -> constr) (v : constr) :=
  let ux := inctx_p (head_binder_ident p) t (fun xx => inctx (Fresh.in_goal @H) (mk_app p xx) u) in
  lazy_match! (Std.eval_hnf (Constr.type ux)) with
  | (forall x H, True) => 'I
  | _ => '(Exists_impl_strong_transparent $t _ _ $l $ux $v)
  end.

(*
Ltac2 mk_exists_impl_smart (t : constr) (p : constr) (u : constr -> constr) (v : constr) :=
  let ux := inctx_p (head_binder_ident p) t (fun xx => inctx (Fresh.in_goal @H) (mk_app p xx) u) in
  lazy_match! (Std.eval_hnf (Constr.type ux)) with
  | (forall x H, True) => 'I
  | _ => '(exists_impl_strong_transparent $t _ _ $ux $v)
  end.
 *)


Ltac2 log (c : constr) := Message.print (typed_constr_message c).
Ltac2 logged (r : constr) := log r; r.
Ltac2 log_context () := Message.print (Message.of_string "Context:"); Message.print (message_of_hyps ()).

Ltac2 rec is_ind_prefix (ind : constr) (t : constr) (args : constr list) :=
  (* Assumes t is in hnf *)
  if Constr.equal t ind then
    Some (List.rev args)
  else
    lazy_match! t with
    | ?t1 ?t2 => is_ind_prefix ind t1 (t2 :: args)
    | _ => None
    end.

Ltac2 rec is_ind_prefix_l (inds : constr list) (t : constr) (l : 'a list) :=
  match inds with
  | [] => None
  | ind :: inds =>
    match is_ind_prefix ind t [] with
    | Some args => Some (args, List.hd l)
    | None => is_ind_prefix_l inds t (List.tl l)
    end
  end.

Ltac2 rec applist (c : constr) (l : constr list) :=
  match l with
  | [] => c
  | x :: l => mk_app (applist c l) x
  end.

Ltac2 rec constrind_hyp (v : constr) (inds : constr list) (hrecs : constr list) :=
  let t := Std.eval_hnf (Constr.type v) in
  match is_ind_prefix_l inds t hrecs with
  | Some argshrec => let (args, hrec) := argshrec in mk_app (applist hrec args) v
  | None =>
    lazy_match! t with
    | list ?a => mk_Forall_proof_smart (Fresh.in_goal @x) a (fun x => constrind_hyp x inds hrecs) v
    | @Forall ?t ?p ?l =>
      mk_Forall_impl_smart t p l (fun h => constrind_hyp h inds hrecs) v
    | @Forall2 ?t1 ?t2 ?p ?l1 ?l2 =>
      mk_Forall2_impl_smart t1 t2 p l1 l2 (fun h => constrind_hyp h inds hrecs) v
    | @Forall3 ?t1 ?t2 ?t3 ?p ?l1 ?l2 ?l3 =>
      mk_Forall3_impl_smart t1 t2 t3 p l1 l2 l3 (fun h => constrind_hyp h inds hrecs) v
    | @if_Some ?t ?p ?x =>
      mk_if_Some_impl_smart t p x (fun h => constrind_hyp h inds hrecs) v
    | @if_Some2 ?t1 ?t2 ?p ?x ?y =>
      mk_if_Some2_impl_smart t1 t2 p x y (fun h => constrind_hyp h inds hrecs) v
    | @if_Some3 ?t1 ?t2 ?t3 ?p ?x ?y ?z =>
      mk_if_Some3_impl_smart t1 t2 t3 p x y z (fun h => constrind_hyp h inds hrecs) v
    | @step_one ?t ?r ?l1 ?l2 =>
      mk_step_one_impl_smart t r l1 l2 (fun h => constrind_hyp h inds hrecs) v
    | @Exists ?t ?p ?l =>
      mk_Exists_impl_smart t p l (fun h => constrind_hyp h inds hrecs) v
(*    | @ex ?t ?p =>
      mk_exists_impl_smart t p (fun h => constrind_hyp h inds hrecs) v *)
    | (?a * ?b)%type =>
      mk_and_proof_smart
        (constrind_hyp (mk_app 'fst v) inds hrecs)
        (constrind_hyp (mk_app 'snd v) inds hrecs)
    | ?a /\ ?b =>
      mk_and_proof_smart
        (constrind_hyp (mk_app 'proj1_transparent v) inds hrecs)
        (constrind_hyp (mk_app 'proj2_transparent v) inds hrecs)
    | forall (x : ?t1), @?t2 x =>
      mk_forall_proof_smart (head_binder_ident t) t1 (fun x => constrind_hyp (mk_app v x) inds hrecs)
    | _ => 'I
    end
  end.

Ltac2 add1 (t : constr) (l : constr list) :=
  lazy_match! (Std.eval_hnf (Constr.type t)) with
  | True => l
  | _ => t :: l
  end.

Ltac2 maybe_app (t1 : constr) (t2 : constr) :=
  lazy_match! (Constr.type (Constr.type t2)) with
  | Prop => t1
  | _ => mk_app t1 t2
  end.

Ltac2 rec constrind1 (c : constr) (cstr : constr) (cstrhyp : constr) (inds : constr list) (ps : constr list) (hrecs : constr list) (args : constr list) (args_recs : constr list) :=
  let c := Std.eval_hnf c in
  lazy_match! c with
  | forall (x : ?t1), @?t2 x =>
    let x := head_binder_ident c in
    inctx_p x t1 (fun xx =>
      constrind1 (mk_app t2 xx) cstr cstrhyp inds ps hrecs (xx :: args) (add1 (constrind_hyp xx inds hrecs) args_recs)
    )
  | ?c =>
    let nt := applist (applist cstrhyp args) args_recs in
    match is_ind_prefix_l inds (Constr.type (applist cstr args)) ps with
    | None => Control.throw Assertion_failure
    | Some targsp =>
      let (targs, p) := targsp in
      Std.unify (Constr.type nt) (maybe_app (applist p targs) (applist cstr args));
      nt
    end
  end.

Ltac2 get_constructors_base (ind : inductive) (inst : instance) (args : constr list) :=
  List.init (Ind.nconstructors (Ind.data ind))
            (fun i => let c := Ind.get_constructor (Ind.data ind) i in
                   applist (Constr.Unsafe.make (Constr.Unsafe.Constructor c inst)) (List.rev args)
            ).

Ltac2 rec split_ind (c : constr) (args : constr list) :=
  lazy_match! (Std.eval_hnf c) with
  | ?t1 ?t2 => split_ind t1 (t2 :: args)
  | ?c => match Constr.Unsafe.kind c with
         | Constr.Unsafe.Ind ind inst => (ind, inst, args)
         | _ => Control.throw (Invalid_argument (Some (Message.of_constr c)))
         end
  end.

Ltac2 get_constructors (c : constr) :=
  let (ind, inst, args) := split_ind c [] in
  get_constructors_base ind inst args.

(*
Ltac2 rec copy_string_from (s1 : string) (s2 : string) (i : int) (j : int) :=
  if Int.equal i (String.length s1) then () else (
      String.set s2 j (String.get s1 i);
      copy_string_from s1 s2 (Int.add i 1) (Int.add j 1)
    ).

Ltac2 concat_string (s1 : string) (s2 : string) :=
  let s3 := String.make (Int.add (String.length s1) (String.length s2)) (Char.of_int 0) in
  copy_string_from s1 s3 0 0;
  copy_string_from s2 s3 0 (String.length s1);
  s3.

Ltac2 named_ident (s : string) := match Ident.of_string s with Some i => i | None => @_unnamed_ end.
 *)

Ltac2 rec ncontext (l : constr list) (l2 : constr list) (tac : constr list -> constr) :=
  match l with
  | [] => tac (List.rev l2)
  | _ :: l => inctx_p (Fresh.in_goal @H) '(_ : Prop) (fun h => ncontext l (h :: l2) tac)
  end.

Ltac2 rec nabs (n : int) (c : constr) :=
  if Int.equal n 0 then c else '(fun _ => ltac2:(Control.refine (fun () => nabs (Int.sub n 1) c))).

Ltac2 rec ind_principle_p (t : constr) :=
  lazy_match! (Constr.type t) with
  | forall (x : ?t1), _ =>
    let x := head_binder_ident (Constr.type t) in
    make_forall (inctx x t1 (fun xx => ind_principle_p (mk_app t xx)))
  | Set => '(($t -> Prop) : Prop)
  | Type => '(($t -> Prop) : Prop)
  | Prop => 'Prop
  end.

Ltac2 rec forall_principle (t : constr) (p : constr) :=
  force_prop (fun () =>
  lazy_match! (Constr.type t) with
  | forall (x : ?t1), _ =>
    let x := head_binder_ident (Constr.type t) in
    make_forall (inctx x t1 (fun xx => forall_principle (mk_app t xx) (mk_app p xx)))
  | Set => '(forall (t : $t), $p t)
  | Type => '(forall (t : $t), $p t)
  | Prop => '(($t -> $p) : Prop)
  end).

Ltac2 rec intro_hyp (name : ident) (c : constr) (tac : constr -> constr) :=
  force_prop_t (fun () =>
  lazy_match! (Constr.type c) with
  | forall (x : ?t1), _ =>
    inctx (head_binder_ident (Constr.type c)) t1 (fun xx => intro_hyp name (mk_app c xx) tac)
  | _ => inctx name c tac
  end).

Ltac2 rec rec_pos (t : constr) :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.Prod _ t => Int.add 1 (rec_pos t)
  | _ => 0
  end.

Ltac2 rec eta_expand (c : constr) (p : constr) :=
  lazy_match! (Constr.type c) with
  | forall (x : ?t1), _ =>
    let x := head_binder_ident (Constr.type c) in
    inctx x t1 (fun xx => eta_expand (mk_app c xx) (mk_app p xx))
  | Prop => '(fun (_ : $c) => $p)
  | Set => '(fun (t : $c) => $p t)
  | Type => '(fun (t : $c) => $p t)
  end.

Ltac2 rec fresh_n (n : int) (x : ident) (s : Fresh.Free.t) :=
  if Int.equal n 0 then [] else
    let y := Fresh.fresh s x in
    y :: fresh_n (Int.sub n 1) x (Fresh.Free.union s (Fresh.Free.of_ids [y])).

Ltac2 rec fresh_n_goal (n : int) (x : ident) := fresh_n n x (Fresh.Free.of_goal ()).

Ltac2 inctxn (names : ident list) (ts : constr list) (body : constr list -> constr) :=
  List.fold_right2 (fun name t tac l => inctx name t (fun x => tac (x :: l))) (fun l => body (List.rev l)) names ts [].

Ltac2 ncontext_l (cstrsl : constr list list) (body : constr list list -> constr) :=
  List.fold_right (fun cstrs tac lhl => ncontext cstrs [] (fun lhyps => tac (lhyps :: lhl))) (fun l => body (List.rev l)) cstrsl [].

Ltac2 mkfix1 (guarded_arg : int) (name : ident) (t : constr) (body : constr -> constr) :=
  let (b, body) :=
      match Constr.Unsafe.kind (inctx name t body) with
      | Constr.Unsafe.Lambda b body => (b, body)
      | _ => Control.throw Assertion_failure
      end
  in
  Constr.Unsafe.make (Constr.Unsafe.Fix (Array.make 1 guarded_arg) 0 (Array.make 1 b) (Array.make 1 body)).

Ltac2 rec get_body (names : ident list) (bds : binder list) (t : constr) :=
  match names with
  | [] => (List.rev bds, t)
  | _ :: names =>
    match Constr.Unsafe.kind t with
    | Constr.Unsafe.Lambda b body => get_body names (b :: bds) body
    | _ => Control.throw Assertion_failure
    end
  end.

(* Ltac2 mkprod u v := '(conj _ _ $u $v). *)
Ltac2 mkprod u v :=
  '(conj $u $v).

Ltac2 rec mkprodn (l : constr list) :=
  match List.tl l with
  | [] => List.hd l
  | _ => mkprod (List.hd l) (mkprodn (List.tl l))
  end.

Ltac2 rotate_left (l : 'a list) (n : int) :=
  List.append (List.skipn n l) (List.firstn n l).
Ltac2 rotate_right (l : 'a list) (n : int) :=
  rotate_left l (Int.sub (List.length l) n).

Ltac2 mkfix_one (guarded_arg : int list) (names : ident list) (ts : constr list) (body : (constr list -> constr) list) (n : int) :=
  let ts := List.map rebuild_prod_cast ts in
  let bodies := List.map rebuild_prod_cast (List.map (inctxn names ts) body) in
  (* List.iter Message.print (List.map show_constr_kind ts);
  List.iter log ts; List.iter log (List.map Constr.type bodies); *)
  let (binders, _) := get_body names [] (List.hd bodies) in
  let binders := Array.of_list binders in
  let guarded_arg := Array.of_list guarded_arg in
  let bodies := Array.of_list (List.map (fun body => let (_, body) := (get_body names [] body) in body) bodies) in
  Constr.Unsafe.make (Constr.Unsafe.Fix guarded_arg n binders bodies).

Ltac2 mkfix_one' (guarded_arg : int list) (names : ident list) (ts : constr list) (body : (constr list -> constr) list) (n : int) :=
  mkfix_one (rotate_left guarded_arg n) (rotate_left names n) (rotate_left ts n) (rotate_left (List.map (fun f l => f (rotate_right l n)) body) n) 0.

Ltac2 mkfix (guarded_arg : int list) (names : ident list) (ts : constr list) (body : (constr list -> constr) list) :=
  mkprodn (List.init (List.length names) (fun n => mkfix_one guarded_arg names ts body n)).

Ltac2 map3 f l1 l2 l3 := List.map2 (fun a (b, c) => f a b c) l1 (List.combine l2 l3).
Ltac2 map4 f l1 l2 l3 l4 := map3 (fun a b (c, d) => f a b c d) l1 l2 (List.combine l3 l4).
Ltac2 map5 f l1 l2 l3 l4 l5 := map4 (fun a b c (d, e) => f a b c d e) l1 l2 l3 (List.combine l4 l5).

Ltac2 gen_ind_principle (cl : constr list) :=
  let n := List.length cl in
  let indstl := List.map (fun c => split_ind c []) cl in
  let cstrsl := List.map (fun (ind, inst, args) => get_constructors_base ind inst args) indstl in
  inctxn (fresh_n_goal n @P) (List.map ind_principle_p cl) (fun pl =>
    ncontext_l cstrsl (fun lhypsl =>
      mkfix (List.map (fun c => rec_pos (Constr.type c)) cl) (fresh_n_goal n @Hrec) (List.map2 forall_principle cl pl)
            (map5 (fun c (ind, _, _) => fun p cstrs lhyps hrecs =>
        intro_hyp (Fresh.in_goal @x) c (fun xx =>
          let branches := List.map2 (fun cstr hcstr => force_prop_t (fun () => rebuild_lam (constrind1 (Constr.type cstr) cstr hcstr cl pl hrecs [] []))) cstrs lhyps in
          (* log (rebuild_lam (eta_expand c p)); *)
          force_prop_t (fun () => Constr.Unsafe.make
            (Constr.Unsafe.Case
               (Constr.Unsafe.case ind)
               (rebuild_lam (eta_expand c p))
               Constr.Unsafe.NoInvert
               xx
               (Array.of_list branches)))
         )) cl indstl pl cstrsl lhypsl)
    )
  ).

Notation "'Induction' 'For' [ x ]" := ltac2:(let l := [x] in Control.refine (fun () => gen_ind_principle (List.map Constr.pretype l))) (at level 0, only parsing).
Notation "'Induction' 'For' [ x ; y ]" :=
  ltac2:(let l := [x; y] in Control.refine (fun () => gen_ind_principle (List.map Constr.pretype l))) (at level 0, only parsing).
Notation "'Induction' 'For' [ x ; y ; z ]" :=
  ltac2:(let l := [x; y; z] in Control.refine (fun () => gen_ind_principle (List.map Constr.pretype l))) (at level 0, only parsing).
Notation "'Induction' 'For' [ x ; y ; z ; w ]" :=
  ltac2:(let l := [x; y; z; w] in Control.refine (fun () => gen_ind_principle (List.map Constr.pretype l))) (at level 0, only parsing).
Notation "'Induction' 'For' [ x ; y ; z ; w ; t ]" :=
  ltac2:(let l := [x; y; z; w; t] in Control.refine (fun () => gen_ind_principle (List.map Constr.pretype l))) (at level 0, only parsing).

(*
Inductive even : nat -> Prop :=
| even_O : even O
| even_SS : forall n, even n -> even (S (S n)).
Definition a := Induction For [ even ].
Definition b := a even even_O (fun n _ Hrec => even_SS n Hrec).
Check b.
Goal True.

  log (Constr.type 'b).

Check (forall (x : nat), Prop).
*)
