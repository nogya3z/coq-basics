Inductive rgb : Type :=
  | red
  | green
  | blue.
Inductive color : Type :=
  | black
  | white
  | primary (p : rgb).

Definition monochrome (c : color) : bool :=
  match c with
  | black => true
  | white => true
  | primary p => false

  end.

Definition isred (c : color) : bool :=
  match c with
  | black => false
  | white => false
  | primary red => true
  | primary _ => false
  end.

Module Playground.
  Definition foo : rgb := blue.
End Playground.

Definition foo : bool := true.

Check Playground.foo : rgb.

Check foo : bool.

Inductive bit : Type :=
  | B1
  | B0.

Inductive nybble : Type :=
  | bits (b0 b1 b2 b3 : bit).

Check (bits B1 B0 B1 B0): nybble.

Definition all_zero (nb : nybble) : bool :=
  match nb with
  | (bits B0 B0 B0 B0) => true
  | (bits _ _ _ _) => false
  end.

Compute (all_zero (bits B1 B0 B1 B0)).

Compute (all_zero (bits B0 B0 B0 B0)).

Module NatPlayground.

Inductive nat : Type :=
  | O
  | S (n : nat).

Inductive otherNat : Type :=
  | stop
  | tick (foo : otherNat).

Definition pred (n : nat) : nat :=
  match n with
  | O => O
  | S n' => n'
  end.

End NatPlayground.

Check (S (S (S (S O)))).

Definition minustwo (n : nat) : nat :=
  match n with
  | O => O
  | S O => O
  | S (S n') => n'
  end.
Compute (minustwo 1).

Definition plusone (n : nat) : nat :=
  match n with
  | O => S O
  | n' => S n'
  end.

Definition plustwo (n : nat) : nat :=
  match n with
  | n' => S (S n')
  end.

Compute (plustwo 100).

Fixpoint even (n:nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => even n'
  end.

  Definition odd (n:nat) : bool :=
  negb (even n).

Example test_odd1: odd 1 = true.
Proof. simpl. reflexivity. Qed.

Example test_odd2: odd 4 = false.
Proof. simpl. reflexivity. Qed.


(* add n to m; if n==0, return m*)
(* plus m is defined  as adding S (1) n times*)
Module NatPlayground2.
Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
  | O => m
  | S n' => S (plus n' m)
  end.

Compute (plus 3 2).

Fixpoint mult (n m : nat) : nat :=
  match n with
  | O => O
  | S n' => plus m (mult n' m)
  end.

Example test_mult1: (mult 3 3) = 9.
Proof. simpl. reflexivity. Qed.

Fixpoint minus (n m:nat) : nat :=
  match n, m with
  | O , _ => O
  | S _ , O => n
  | S n', S m' => minus n' m'
  end.

Compute (minus 10 10).

Fixpoint exp (base power : nat) : nat :=
  match power with
  | O => S O
  | S p => mult base (exp base p)
  end.

Compute (exp 10 2).

(* Exercise *)
(* Recall the standard mathematical factorial function:
       factorial(0)  =  1
       factorial(n)  =  n * factorial(n-1)     (if n>0)*)

(* Exercise 
Fixpoint fact (n : nat) : nat :=
  match n with
  | O => S O
  | S O => S O
  | n' => mult n (fact(n'))
  end.
*)

Fixpoint factorial (n : nat) : nat :=
  match n with
  | O => S O
  | S O => S O
  | S n' => mult n (factorial n')
  end. 

Example test_factorial1: (factorial 3) = 6.
Example test_factorial2: (factorial 5) = (mult 10 12).

Notation "x + y" := (plus x y)
                       (at level 50, left associativity)
                       : nat_scope.

Notation "x - y" := (minus x y)
                       (at level 50, left associativity)
                       : nat_scope.
Notation "x * y" := (mult x y)
                       (at level 40, left associativity)
                       : nat_scope.


Check ((0 + 1) + 1) : nat.

Example test_plus_sign: (3+5) = 8.
Proof. simpl. reflexivity. Qed.

Fixpoint eqb (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => eqb n' m'
            end
  end.

Fixpoint leb (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => leb n' m'
      end
  end.

Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.
Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.


Fixpoint ltb (n m : nat) : bool :=
  match n, m with
  | O, O => false
  | O, S _ => true
  | _, O => false
  | S n', S m' => ltb n' m'
  end.

Definition ltb1 (n m : nat) : bool :=
  match m - n with
  | O => false 
  | S _ => true
  end.

Notation "x <? y" := (ltb x y) (at level 70) : nat_scope.
Example test_ltb1: (ltb 2 2) = false.
Proof. simpl. reflexivity. Qed.
Example test_ltb2: (ltb 2 4) = true.
Proof. simpl. reflexivity. Qed.
Example test_ltb3: (ltb 4 2) = false.
Proof. simpl. reflexivity. Qed.
Example test_ltb4: (ltb 0 0) = false.
Proof. simpl. reflexivity. Qed.

Example test_ltb11: (ltb1 2 2) = false.
Proof. simpl. reflexivity. Qed.
Example test_ltb12: (ltb1 2 4) = true.
Proof. simpl. reflexivity. Qed.
Example test_ltb13: (ltb1 4 2) = false.
Proof. simpl. reflexivity. Qed.
Example test_ltb14: (ltb1 0 0) = false.
Proof. simpl. reflexivity. Qed.


Theorem plus_O_n : forall n : nat, 0 + n = n.
Proof.
  intros n. simpl. reflexivity. Qed.

(*Example and Theorem 
  (and a few others, including Lemma, Fact, and Remark) mean pretty much the same thing to Coq.*)

Theorem plus_id_example : forall n m:nat,
  n = m ->
  n + n = m + m.
Proof.
  (* move both quantifiers into the context: *)
  intros n m.
  (* move the hypothesis into the context: That is the Hypthesis includes, n=m*)
  (*In otherwords, the left side of -> is the hypothesis*)
  intros H.
  (* rewrite takes takes a proposition, which is something with an '=' *)
  (* The -> below replaces n with m *)
  rewrite -> H.
  reflexivity. Qed.

  Check plus_id_example.


Theorem plus_id_exercise : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
Proof.
  intros n m o.
  intros H1 H2.
  rewrite -> H1.
  rewrite -> H2.
  reflexivity. Qed.
  
  Check plus_id_exercise.

Check mult_n_O.

Theorem mult_n_0_m_0 : forall p q: nat,
  (p * 0) + (q * 0) = 0.
Proof.
  intros p q.
  rewrite <- mult_n_O.
  rewrite <- mult_n_O.
  reflexivity. Qed.






Check  mult_n_Sm.


Check  mult_n_O.

Theorem mult_n_1 : forall p : nat,
  p * 1 = p.
Proof.
  (* Use mult_n_0 *)
  intros p.
  rewrite <- mult_n_Sm.
  rewrite <- mult_n_O.
  (* Use mult_n_Sm *)
  (* FILL IN HERE *) Admitted.


Theorem plus_1_neq_0_firsttry : forall n : nat,
  (* =? is eqb which returns bool (true) if n == m *)
  (n + 1) =? 0 = false.
Proof.
  intros n.
  simpl. (* does nothing! *)
Abort.


(* Desctruct: tactic that tells Coq to consider, separately,
the cases where n = O and where n = S n'*)
Theorem plus_1_neq_0 : forall n : nat,
  (n + 1) =? 0 = false.
Proof.
  intros n. destruct n as [| n'] eqn:E.
  - reflexivity.
  - reflexivity. Qed.
