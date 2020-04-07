Require Import Misc.
Require Import List.
Require Import Freevar.
Require Import Term.
Require Import FEnv.

Inductive nfval :=
| NFFreeVar : freevar -> nfval
| NFStructApp : nfval -> nfval_or_lam -> nfval

with nfval_or_lam :=
| NFVal : nfval -> nfval_or_lam
| NFLam : freevar -> nfval_or_lam -> nfval_or_lam.

Inductive envitem :=
| EVal : nfval -> envitem
| ELazy : term -> envitem
| ELam : term -> freevar -> envitem.

Inductive cont :=
| KNil : cont
| KUpdateLazy : freevar -> list term -> cont -> cont
| KUpdateLam : term -> freevar -> cont -> cont
| KApp : nfval -> list term -> cont -> cont.

Record state := mkState {
  st_code : envitem ;
  st_stack : list term ;
  st_env : list (freevar * envitem) ;
  st_cont : cont ;
  st_lamnf : list (freevar * nfval_or_lam) ;
  st_usedvars : list freevar ;
}.

Inductive red : state -> state -> Prop :=
| red_app : forall t u e pi K W L,
    red {| st_code := ELazy (app t u) ; st_stack := pi ; st_env := e ; st_cont := K ; st_lamnf := W ; st_usedvars := L |}
        {| st_code := ELazy t ; st_stack := u :: pi ; st_env := e ; st_cont := K ; st_lamnf := W ; st_usedvars := L |}
| red_lam : forall t e pi K W L y,
    y \notin L ->
    red {| st_code := ELazy (lam t) ; st_stack := pi ; st_env := e ; st_cont := K ; st_lamnf := W ; st_usedvars := L |}
        {| st_code := ELam t y ; st_stack := pi ; st_env := e ; st_cont := K ; st_lamnf := W ; st_usedvars := y :: L |}
| red_redex : forall t u e pi K W L x y,
    x \notin L ->
    red {| st_code := ELam t y ; st_stack := u :: pi ; st_env := e ; st_cont := K ; st_lamnf := W ; st_usedvars := L |}
        {| st_code := ELazy (t ^ x) ; st_stack := pi ; st_env := (x, ELazy u) :: e ; st_cont := K ; st_lamnf := W ; st_usedvars := x :: L |}
| red_var_open : forall x e pi K W L,
    env_find e x = None ->
    red {| st_code := ELazy (fvar x) ; st_stack := pi ; st_env := e ; st_cont := K ; st_lamnf := W ; st_usedvars := L |}
        {| st_code := EVal (NFFreeVar x) ; st_stack := pi ; st_env := e ; st_cont := K ; st_lamnf := W ; st_usedvars := L |}
| red_var_val : forall x e v pi K W L,
    env_find e x = Some (EVal v) ->
    red {| st_code := ELazy (fvar x) ; st_stack := pi ; st_env := e ; st_cont := K ; st_lamnf := W ; st_usedvars := L |}
        {| st_code := EVal v ; st_stack := pi ; st_env := e ; st_cont := K ; st_lamnf := W ; st_usedvars := L |}
| red_var_lazy : forall x e t pi K W L,
    env_find e x = Some (ELazy t) ->
    red {| st_code := ELazy (fvar x) ; st_stack := pi ; st_env := e ; st_cont := K ; st_lamnf := W ; st_usedvars := L |}
        {| st_code := ELazy t ; st_stack := nil ; st_env := e ; st_cont := KUpdateLazy x pi K ; st_lamnf := W ; st_usedvars := L |}
| red_var_lam : forall x e t y pi K W L,
    env_find e x = Some (ELam t y) ->
    red {| st_code := ELazy (fvar x) ; st_stack := pi ; st_env := e ; st_cont := K ; st_lamnf := W ; st_usedvars := L |}
        {| st_code := ELam t y ; st_stack := pi ; st_env := e ; st_cont := K ; st_lamnf := W ; st_usedvars := L |}
| red_app_val : forall v e u pi K W L,
    red {| st_code := EVal v ; st_stack := u :: pi ; st_env := e ; st_cont := K ; st_lamnf := W ; st_usedvars := L |}
        {| st_code := ELazy u ; st_stack := nil ; st_env := e ; st_cont := KApp v pi K ; st_lamnf := W ; st_usedvars := L |}
| red_lam_deepen : forall t x e K W L,
    env_find W x = None ->
    red {| st_code := ELam t x ; st_stack := nil ; st_env := e ; st_cont := K ; st_lamnf := W ; st_usedvars := L |}
        {| st_code := ELazy (t ^ x) ; st_stack := nil ; st_env := e ; st_cont := KUpdateLam t x K ; st_lamnf := W ; st_usedvars := L |}
| red_cont_app_val : forall v1 v2 pi K e W L,
    red {| st_code := EVal v1 ; st_stack := nil ; st_env := e ; st_cont := KApp v2 pi K ; st_lamnf := W ; st_usedvars := L |}
        {| st_code := EVal (NFStructApp v2 (NFVal v1)) ; st_stack := pi ; st_env := e ; st_cont := K ; st_lamnf := W ; st_usedvars := L |}
| red_cont_app_lam : forall t x body v pi K e W L,
    env_find W x = Some body ->
    red {| st_code := ELam t x ; st_stack := nil ; st_env := e ; st_cont := KApp v pi K ; st_lamnf := W ; st_usedvars := L |}
        {| st_code := EVal (NFStructApp v (NFLam x body)) ; st_stack := pi ; st_env := e ; st_cont := K ; st_lamnf := W ; st_usedvars := L |}
| red_cont_update_lam_val : forall t v x K e W L,
    red {| st_code := EVal v ; st_stack := nil ; st_env := e ; st_cont := KUpdateLam t x K ; st_lamnf := W ; st_usedvars := L |}
        {| st_code := ELam t x ; st_stack := nil ; st_env := e ; st_cont := K ; st_lamnf := (x, NFVal v) :: W ; st_usedvars := L |}
| red_cont_update_lam_lam : forall t1 t2 y body x K e W L,
    env_find W y = Some body ->
    red {| st_code := ELam t2 y ; st_stack := nil ; st_env := e ; st_cont := KUpdateLam t1 x K ; st_lamnf := W ; st_usedvars := L |}
        {| st_code := ELam t1 x ; st_stack := nil ; st_env := e ; st_cont := K ; st_lamnf := (x, NFLam y body) :: W ; st_usedvars := L |}
| red_cont_update_lazy_val : forall v x pi e K W L,
    red {| st_code := EVal v ; st_stack := nil ; st_env := e ; st_cont := KUpdateLazy x pi K ; st_lamnf := W ; st_usedvars := L |}
        {| st_code := EVal v ; st_stack := pi ; st_env := update_env e x (EVal v) ; st_cont := K ; st_lamnf := W ; st_usedvars := L |}
| red_cont_update_lazy_lam : forall t y x pi e K W L,
    red {| st_code := ELam t y ; st_stack := nil ; st_env := e ; st_cont := KUpdateLazy x pi K ; st_lamnf := W ; st_usedvars := L |}
        {| st_code := ELam t y ; st_stack := pi ; st_env := update_env e x (ELam t y) ; st_cont := K ; st_lamnf := W ; st_usedvars := L |}
.

Fixpoint read_nfval (v : nfval) :=
  match v with
  | NFFreeVar x => fvar x
  | NFStructApp v1 v2 => app (read_nfval v1) (read_nfval_or_lam v2)
  end

with read_nfval_or_lam (v : nfval_or_lam) :=
  match v with
  | NFVal v => read_nfval v
  | NFLam x v => lam (closeb 0 x (read_nfval_or_lam v))
  end.

Definition read_envitem (ei : envitem) :=
  match ei with
  | EVal v => read_nfval v
  | ELam t x => lam t
  | ELazy t => t
  end.

Fixpoint read_stack t pi :=
  match pi with
  | nil => t
  | u :: pi => read_stack (app t u) pi
  end.


Fixpoint nfval_ind2 (P : nfval -> Prop) (Q : nfval_or_lam -> Prop)
         (Hfree : forall x, P (NFFreeVar x)) (Happ : forall v1 v2, P v1 -> Q v2 -> P (NFStructApp v1 v2))
         (Hval : forall v, P v -> Q (NFVal v)) (Hlam : forall x v, Q v -> Q (NFLam x v)) v : P v :=
  match v with
  | NFFreeVar x => Hfree x
  | NFStructApp v1 v2 => Happ v1 v2 (nfval_ind2 P Q Hfree Happ Hval Hlam v1) (nfval_or_lam_ind2 P Q Hfree Happ Hval Hlam v2)
  end

with nfval_or_lam_ind2 (P : nfval -> Prop) (Q : nfval_or_lam -> Prop)
         (Hfree : forall x, P (NFFreeVar x)) (Happ : forall v1 v2, P v1 -> Q v2 -> P (NFStructApp v1 v2))
         (Hval : forall v, P v -> Q (NFVal v)) (Hlam : forall x v, Q v -> Q (NFLam x v)) v : Q v :=
  match v with
  | NFVal v => Hval v (nfval_ind2 P Q Hfree Happ Hval Hlam v)
  | NFLam x v => Hlam x v (nfval_or_lam_ind2 P Q Hfree Happ Hval Hlam v)
  end.

Definition nfval_and_lam_ind2 P Q Hfree Happ Hval Hlam :=
  conj (fun v => nfval_ind2 P Q Hfree Happ Hval Hlam v) (fun v => nfval_or_lam_ind2 P Q Hfree Happ Hval Hlam v).


Lemma nfval_and_lam_lc :
  (forall v, lc (read_nfval v)) /\ (forall v, lc (read_nfval_or_lam v)).
Proof.
  apply nfval_and_lam_ind2.
  - intros; simpl; constructor.
  - intros; simpl; constructor; assumption.
  - intros; simpl; assumption.
  - intros; simpl. apply lc_lam_body. apply closeb_body. assumption.
Qed.

Definition nfval_or_lam_lc := proj2 nfval_and_lam_lc.
