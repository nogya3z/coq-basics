Require Import Coq.Sets.Ensembles.
Require Import Coq.Arith.Arith.
Require Import Coq.Logic.Classical_Prop.

(* https://coq.inria.fr/doc/v8.9/stdlib/Coq.Sets.Ensembles.html#In *)
(* Recall that U is a Prop*)




(* Basics*)
(* Sets *)
(* Set is a predefined keyword in Coq that
 we can think of as meaning all program data types *)
 (* Coq documentation describes Set as being the 
 type of program specifications, which describe computations. *)
(*
 Prop is also a type.
 Prop (proposition): any statement we might try to prove in Coq
*)

Variable S : Type.


(* Definition of a set*)
Definition ASet :=
  (* This is to say S implies  Prop *)
  (* In otherwords, S there Prop *)
  S -> Prop.


Check Prop.

Check Type.

Check Ensemble.

Check Empty_set.

Check Full_set.

Check Setminus.

Check nat.

Check Set.

Variable U : Type.

Definition Ensemble := U -> Prop.

Definition In (A:Ensemble) (x:U) : Prop := A x.

Example test1 : In (Singleton x) x = false.
Proof. simpl. reflexivity. Qed.


Inductive Singleton2 (x:U) : Ensemble :=
    In_singleton10 : In (Singleton2 x) x.