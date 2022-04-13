(**
  Standard Assignment:  Binary Tree Analysis
  Made by:              Tobias Sagis & Luuk Spierings
**)

(* Libraries to import *)
Require Import Lia.
Require Import Arith.
Require Import Bool.
Require Import List.

(* Notations *)
Notation "a >=? b" := (Nat.leb b a) (at level 70) : nat_scope. (* Issue with Nat not defining this? *)
Notation "a :: b" := (cons a b). (* Issue with Nat not defining this? *)


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
Fixpoint forall_nodes (P: nat -> Prop) (t: tree) : Prop :=
  match t with
  | leaf => True
  | node l n r => P n /\ forall_nodes P l /\ forall_nodes P r
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
Fixpoint bst (T : tree) : Prop :=
  match T with
  | leaf => True
  | node l n r => 
         forall_nodes (fun x => x < n) l 
      /\ forall_nodes (fun x => x > n) r 
      /\ bst l 
      /\ bst r
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
  | node l n r => 
      if (N <? n) then node (insert N l) n r 
      else if (n <? N) then node l n (insert N r) 
      else node l N r
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
Theorem ltb_reflect : forall x y, reflect (x < y) (x <? y).
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
  In summary; for every predicate P and tree t we check that if the
  bst property holds on P and t, then it should hold on all subsequent
  subnodes below the starting node t.
*)
Theorem forall_nodes_insert : forall (P : nat -> Prop) (t : tree),
    forall_nodes P t -> forall (k : nat), P k -> forall_nodes P (insert k t).
Proof.
  intros.
  induction t.
  simpl.
  intuition.

  inversion H.
  simpl in *.
  destruct H.
  destruct H3.
  destruct H2.

  destruct (k <? n).
  simpl.
  intuition.
  destruct (n <? k).
  simpl.
  intuition.
  simpl.
  intuition.
Qed.


Lemma equal : forall(n1 n2: nat), ~n1 < n2 /\ ~n2 < n1 -> n1 = n2.
Proof.
only 1: intros a; only 1: intro m; only 1: intuition; only 1: Nat.Private_Tac.order.
Qed.

(* Let us now formally prove the validity of the insert function *)
Theorem insert_correct : forall (T : tree) (n : nat), bst T -> bst (insert n T).
Proof.
  (* Apply induction and prove the base case *)
  intros.
  induction T.
  simpl.
  auto.

  (* Now for the step case*)
  inversion H.
  intuition.
  simpl.
  destruct (ltb_reflect n n0).
  constructor.
  apply forall_nodes_insert; assumption.
  split.
  assumption.
  split; assumption.
  destruct (ltb_reflect n0 n).
  simpl.
  split.
  assumption.
  split.
  apply forall_nodes_insert; assumption.
  split; assumption.
  simpl.
  split.
  rewrite (equal n n0).
  assumption.
  intuition.
  split.
  rewrite (equal n n0).
  assumption.
  intuition.
  split; assumption.
Qed.

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

(* 
  Similar to the binary search tree, we define a predicate that 
  should hold on all elements of the list.
*)
Fixpoint forall_elements (P: nat -> Prop) (l: natlist) : Prop :=
  match l with
  | nil => True
  | cons a b => P a /\ forall_elements P b
  end.

(*
  All list elements should satisfy a property defined by predicate P.
*)
Theorem forall_elements_app : forall (P: nat -> Prop) (l1 l2 : natlist),
  forall_elements P l1 -> forall_elements P l2 -> forall_elements P (l1 ++ l2).
Proof.
  induction l1.
  (* Base case *)
  intros.
  simpl.
  auto.

  (* Step case *)
  intros.
  simpl.
  inversion H.
  split.
  assumption.
  apply IHl1; assumption.
Qed.

(**)
Theorem list_preserves_tree_predicate : forall (P : nat -> Prop) (t : tree),
  forall_nodes P t -> forall_elements P (to_list t).
Proof.
  intros.
  induction t.
  (* Base case *)
  simpl in *.
  assumption.

  (* Step case *)
  simpl.
  split.
  inversion H.
  destruct H1 as [H1 H2].
  assumption.
  apply forall_elements_app.
  simpl in H.
  destruct H as [H1 H2].
  destruct H2 as [H2 H3].
  apply IHt1.
  assumption.
  apply IHt2.
  simpl in H.
  destruct H as [H1 H2].
  destruct H2 as [H2 H3].
  assumption.
Qed.

(* Question 6.
Prove that the result of the sort function is always a binary search tree. *)

Theorem to_bst_produces_bst : forall (T : natlist), bst (to_bst T).
Proof.
intuition.
induction T.
simpl.
trivial.
simpl.
apply insert_correct.
auto.
Qed.

Theorem sort_produces_bst : forall (T : tree), bst (sort T).
Proof.
  intros.
  induction T.
  simpl.
  trivial.
  apply to_bst_produces_bst.
Qed.

(* Question 7.
Given the predicate occurs expressing that an element belongs to a tree, prove
that the sorted version of a tree contains the same elements as the original
one *)

Variables occurs : nat -> tree -> Prop.

(* De occurs moet blijkbaar via een predefined predicate, ipv dat je die zelf moet maken... *)

(*
Theorem forany_node_insert : forall (t : tree)(k : nat),
    occurs k t -> forall(l: nat), occurs k (insert l t).
Proof.
  intros.
  induction t.
  simpl.
  intuition.

  inversion H.
  simpl in *.
  destruct (k <? n).
  simpl.
  intuition.
  destruct (n <? k).
  simpl.
  intuition.
  simpl.
  intuition.
  simpl in *. 
  destruct (k <? n). 
  simpl. 
  intuition. 
  destruct (n <? k). 
  simpl. 
  intuition. 
  simpl. 
  intuition.
Admitted. 

Fixpoint contains (T : natlist) (n: nat) {struct T} : Prop :=
  match T with
  | nil => False
  | cons x xs => x = n \/ contains xs n
  end.

Theorem contains_instead: forall (T : tree)(n : nat), occurs (insert n T) n.
Proof.

intros.

induction T.
simpl.
auto.

simpl.
destruct (n <? n0).
right.
intuition.
destruct (n0 <? n).
right.
intuition.
constructor.
intuition.
Qed.
*)

Theorem sort_contains_same_element : forall (T : tree)(n : nat), occurs n T <-> occurs n (sort T).
Proof.
  intros.
  intuition.
  induction T.

  intuition.

  simpl in *.
  intuition.

  unfold sort.
  simpl.
  subst.

  
  intuition.
  unfold sort.
  simpl.

Admitted.



(* ------------------- Part 2 ------------------- *)


(* Q1. Define a function treeMin that will return the value of the minimal node in a
tree. You may want to use Coq.Arith.Min for the minimum function. Note
that every function in Coq needs to be total and you will need to decide what
this function should return applied on an empty tree. To do this, use the
option type. Check the definition of option by doing Print option. *)

Print option.

Definition min_option (no1 no2 : option nat) (n : nat) :=
  match no1, no2 with 
   | None, None       => n
   | None, Some r     => min r n
   | Some l, None     => min l n
   | Some l, Some r   => min l (min r n)
  end.

Fixpoint treeMin_option(T: tree) : option nat :=
  match T with
  | leaf => None
  | node l n r => Some (min_option (treeMin_option l) (treeMin_option r) n)
  end.

Definition treeMin(T: tree) : nat :=
  match (treeMin_option T) with
  | None => 0
  | Some n => n
  end.

Eval compute in (treeMin test_type).



(* Q2. Given the predicate occurs expressing that an element belongs to a tree,
prove correctness of the treeMin function, i.e. prove that:
– the minimal element belongs to the tree and
– that the values in all nodes are greater or equal than the minimal value. *)


Theorem min_occur_proof : forall (T : tree), occurs (treeMin T) T.
Proof.
  intros.
  induction T.
  compute.
Admitted.


(* Q3. Define a function leftmost that given a tree will return a value of its leftmost node. *)

Fixpoint leftmost(T: tree) : nat :=
  match T with
  | leaf => 0
  | node leaf n r => n
  | node l n r => leftmost l
  end.

Eval compute in (leftmost test_type).


(* Q4. Prove that the minimal element of a binary search tree (use the predicate bst
on tree) is its leftmost node *)

Theorem bst_left_min : forall (T : tree), bst T -> leftmost T = treeMin T.
Proof.
intuition.
induction T.
auto.
simpl in *.
intuition.

Admitted.



(* Q5. Define a function search that given a binary search tree will check whether a
given natural number occurs in the tree. It should use the fact that the tree
is a binary search tree so it should look only on one branch of a tree, instead
of on all of its nodes. *)

Fixpoint search (N: nat)(T: tree) : Prop :=
  match T with
  | leaf => False
  | node l n r => 
      if (n =? n) then True 
      else if (N <? n) then search N l 
      else search N r
  end.


Theorem search_correct: forall (t: tree)(n : nat), bst t -> (occurs n t <-> search n t).
Proof.
intuition.
induction t.
simpl in *.



Admitted.



