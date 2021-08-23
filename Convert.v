Require Import List.
Require Import Arith.
Require Import Freevar.
Require Import Misc.
Require Import Psatz.
Require Import Star.
Require Import Coq.Logic.Eqdep_dec.
Require Import FEnv.
Require Import STerm.
Require Import Inductive.
Require Import Beta.

Definition valptr := freevar.
Definition threadptr := freevar.

Definition env := list valptr.

Inductive cont_item :=
| KApp : valptr -> cont_item
| KSwitch : list term -> env -> list (list freevar * valptr) -> cont_item.

Definition cont := list cont_item.

Definition neutral := (freevar * cont * option (valptr * nat))%type.

Inductive value :=
| Thread : threadptr -> value
| Neutral : neutral -> value
| Clos : term -> env -> freevar -> valptr -> value
| Block : nat -> list valptr -> value.

Inductive code :=
| Term : term -> code
| Val : valptr -> code.

