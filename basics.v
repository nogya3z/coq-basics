(* What is inductive? Why? *)
(* Non primitive, user defined data structures*)
(* Constructors used to build other data type*)
(* Similar to Classes/Structs  *)
(* Also we are defining a set of possible values: red, blue, green, etc. *)

Inductive rgb : Type :=
  | red
  | green
  | blue.

Check rgb.

Inductive color : Type :=
  | black
  | white
  | primary (p : rgb).

Check color.

(* So what is something non-inductive? *)
(* Natively defined *)
Check Prop.

(* Could be coded from scratch *)
Check bool.

(* For example...*)
Inductive bool : Type :=
  | true
  | false.

Check nat.

Check Set.


(* Definitions are similar to functions *)
(* is red maps the set of color into the sets of booleans (true/false) *)
Definition isred (c : color) : bool :=
  match c with
  | black => false
  | white => false
  | primary red => true
  | primary _ => false
  end.


(* Here are our first few proofs *)
Example test1 : isred black = false.
Proof. simpl. reflexivity. Qed.

Example test2 : isred white = false.
Proof. simpl. reflexivity. Qed.

Example test3 : isred (primary red) = true.
Proof. simpl. reflexivity. Qed.
(* There are different proof techniques that coq uses. this basically checks that one side equals the other *)
(* These are not such exciting proofs, but are stepping stones to more rigorous ones *)


(* See: https://coq.inria.fr/doc/V8.19.2/stdlib/Coq.Init.Nat.html *)
(* Constructive Logic: also called Inutitionist logic*)
(* https://en.wikipedia.org/wiki/Intuitionistic_logic *)
(* In other words you make most of the rules as you go.*)
(* In other words, we are defining all natural numbers, just starting with the definitions of 0 and 1*)


Inductive nat : Type :=
  (* Think of O as the base case*)
  | O
  (* Think of the following line as the inductive scenario*)
  (* S(O), S(S(O)) ... ie 1,2,...*)
  | S (n : nat).
  

(* O is zero, and S is the successor function (ie increments by 1)*)

Definition pred (n : nat) : nat :=
  match n with
  (* By definition, we define that the predecessor of O is simply O*)
  (* This isn't a fact of life,
  but something that we decide to be rules for this particular set of Numbers*)
  | O => O
  | S n' => n'
  end.

Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
  (* If n matches with O,
  Then this effectively becomes  0+m  which is m
  Think of 0+m=m as our base case
  *)
  | O => m
  (* If n is not O,
  Then we recursively call plus on the predecessor.
  S(plus(0 m)) = m+1
  S(S(plus(0 m))) = m+2
  ....etc.
  *)
  | S n' => S (plus n' m)
  end.



