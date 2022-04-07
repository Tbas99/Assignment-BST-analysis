(**
  Standard Assignment:  Binary Tree Analysis
  Made by:              Tobias Sagis & Luuk Spierings
**)

(* Libraries to import *)
Require Import Lia.
Require Import Arith.
Require Import Bool.

(* Notations *)
Notation "a >=? b" := (Nat.leb b a) (at level 70) : nat_scope. (* Issue with Nat not defining this? *)

(* Define a tree type *)
Inductive tree : Set :=
  | leaf : tree
  | node : tree -> nat -> tree -> tree.

Check node (node (node leaf 2 leaf) 5 (node leaf 7 leaf)) 10 (node (node leaf 12 leaf) 16 (node leaf 17 leaf)).

(*
  Before we define the predicate we need some helper function in
  order to establish the validity of the binary search tree properties.
  With this we take a predicate P and check if it holds on all subtree's
  by inductively traversing the subtree's.
*)
Fixpoint bst_prop (P : nat -> tree -> Prop) (T : tree) : Prop :=
  match T with
  | leaf => True (* A leaf trivially satisfies the bst property *)
  | node l n r => P n T /\ bst_prop P l /\ bst_prop P r
  end.

(*
    Define the predicate on tree to express that a tree is sorted.
    With this we mean that the tree is actually a sorted binary tree,
    or simply a binary search tree.
    For a tree to be a binary search tree it must hold that for all
    internal nodes:
    - The key stored must be greater than all the keys in the node's
      left subtree.
    - The key stored must be less than or equal all the keys in the
      node's right subtree.
*)
(*
Fixpoint bst (T : tree) : Prop :=
  match T with
  | leaf => True
  | node l n r => (bst_prop (fun x _ => x < n) l) /\ (bst_prop (fun x _ => (x > n) \/ (x = n)) r) /\ bst l /\ bst r
  end.
*)

Fixpoint bst (T : tree) : Prop :=
  match T with
  | leaf => True
  | node l n r => bst l /\ bst r /\ 
    match l with
    | leaf => True
    | node l_l n_l r_l => (n_l < n)
    end
    /\
    match r with
    | leaf => True
    | node l_r n_r r_r => (n_r = n) \/ (n_r > n)
    end
  end.

(* Check if bst classification is correct *)
Section verify_bst_invariant.

Definition invalid_bst_tree : Prop :=
  bst (node (node leaf 6 leaf) 4 (node leaf 10 leaf)).

Definition valid_bst_tree : Prop :=
  bst (node (node leaf 4 leaf) 6 (node leaf 10 leaf)).

Theorem is_not_bst_tree : ~invalid_bst_tree.
Proof.
  unfold invalid_bst_tree.
  simpl.
  unfold not; intros.
  destruct H as [H1 H2].
  destruct H1 as [H11 H12].
  lia. (* Solves the fact that 6 < 4 is False *)
Qed.

Theorem is_bst_tree : valid_bst_tree.
Proof.
  unfold valid_bst_tree.
  simpl.
  lia. (* Similar to above *)
Qed.

End verify_bst_invariant.

(*
  Define a function that takes a binary search tree and a 
  natural number and inserts the number in the right place
  in the tree.
  So that the insertion does not break the binary search tree
  property.
  Then return the tree.
*)
Fixpoint insert (N : nat) (T : tree) : tree :=
  match T with
  | leaf => node leaf N leaf
  | node l n r => if (N <? n) then node (insert N l) n r else if (N >=? n) then node l n (insert N r) else node l n r
  end.

(* Let us prove the correctness of our insert function *)
Section verify_insert.

Definition test_type : tree :=
  node (node leaf 4 leaf) 6 (node leaf 10 leaf).

(* A test to confirm our intuition *)
Theorem insert_test : (insert 4 (insert 10 (insert 6 (leaf)))) = test_type.
Proof.
  simpl.
  unfold test_type.
  auto.
Qed.

(*
  In order to prove that insert behaves correctly for any
  tree T and node value n, we have to unfold the definition
  for the inductive propositons defined above. 
  In order to prove these structures, we need a way to relate
  a propositon to a boolean.
  Let us define a function that does this for us, using the
  Reflection library in Coq.Bool.

  Note: Since we are mainly interested in the less than (<)
  operator, as defined in our insert function, we shall write
  the corresponding reflection function.
*)
Lemma ltb_reflect : forall x y, reflect (x < y) (x <? y).
Proof.
  intros.
  apply iff_reflect. (* Convert reflect to its value *)
  symmetry.
  apply Nat.ltb_lt. (* Lemma to solve the goal - Defined in Arith *)
Qed.

(* 
  For our formal proof we also need another theorem. This theorem
  states that insert should preserve any predicate P on a node,
  similar to the one we defined for inductively checking the bst
  property.
  In summary; for every predicate P and tree T we check that if the
  bst property holds on P and T, then it should hold on all subsequent
  subnodes below the starting node T.
*)
Theorem bst_prop_insert : forall (P : nat -> tree -> Prop) (T : tree),
     bst_prop P T -> forall (n : nat) (t : tree),
     P n t -> bst_prop P (insert n T).
Proof.
  intros P T.
  induction T.
  intros H1 n t H2.
  simpl. split.
Admitted.

(* Let us now formally prove the validity of the insert function *)
Theorem insert_correct : forall (T : tree) (N : nat), bst T -> bst (insert N T).
Proof.
  (* Apply induction and prove the base case *)
  intros T N.
  induction T.
  intros.
  simpl; auto.

  (* Now for the step case*)
  intros.
  inversion H. (* To discover the cases which must be true for this to hold *)
  simpl.
  destruct H1 as [H1 H2].
  destruct H2 as [H2 H3].
  destruct (ltb_reflect N n). (* Use the reflection function defined above *)
  intuition.
  simpl.
  split.
  assumption.
  split.
  assumption.
  split.
  destruct (insert N T1).
  assumption.
Admitted.


End verify_insert.


(* Question 5.
Define a function sort that takes an arbitrary tree and sorts it, 
i.e. it transforms it into a binary search tree. 
Hint: you can define two auxiliary functions, 
one that stores the elements of a tree in a list 
and one that builds a binary search tree from the elements of a list. *)

Section bst_sort.

Inductive natlist : Set :=
  | nil : natlist
  | cons : nat -> natlist -> natlist.

Fixpoint append (l m : natlist) {struct l} : natlist :=
  match l with
  | nil => m
  | cons x xs => cons x (append xs m)
  end.

Notation "a ++ b" := (append a b).

Fixpoint to_list (T: tree) : natlist :=
  match T with
  | leaf => nil
  | node l n r => cons n ((to_list l) ++ (to_list r))
  end.

Fixpoint to_bst (T : natlist) : tree :=
  match T with
  | nil => leaf
  | cons a b => insert a (to_bst b)
  end.

Definition sort (T : tree) : tree := 
  to_bst (to_list T).

Eval compute in (to_list test_type).
Eval compute in (sort test_type).

(* 
        10
       /
      4
       \
        6
 *)


(* Question 6.
Prove that the result of the sort function is always a binary search tree. *)

Theorem tolist_empty : to_list leaf = nil.
Proof.
simpl.
reflexivity.
Qed.

Theorem sort_produces_bst : forall (T : tree), bst (sort T).
Proof.
intros.
induction T.
simpl.
trivial.
unfold sort.
unfold to_list.
unfold to_bst.
simpl.
Admitted.

(* Question 7.
Given the predicate occurs expressing that an element belongs to a tree, prove
that the sorted version of a tree contains the same elements as the original
one *)

Fixpoint occurs (T : tree) (e: nat) {struct T} : Prop :=
  match T with
  | leaf => False
  | node l n r => n = e \/ occurs l n \/ occurs r n
  end.




Theorem sort_contains_same_element : forall (T : tree)(e : nat), occurs T e <-> occurs (sort T) e.
Proof.
intros.
induction T.
simpl.
tauto.
destruct IHT1.
destruct IHT2.
split.
intros.
simpl in H3.
destruct H3.
unfold sort.
simpl.
Suggest.



Admitted.

Lemma eq_insert: forall (T : tree)(e : nat), occurs (insert e T) e.
Proof.
intros.
induction T.
simpl.
auto.
simpl.

Qed.

End bst_sort.


