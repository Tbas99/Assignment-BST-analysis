(**
  Standard Assignment:  Binary Tree Analysis
  Made by:              Tobias Sagis & Luuk Spierings
**)

(* Define a tree type *)
Inductive tree : Set :=
  | leaf : tree
  | node : tree -> nat -> tree -> tree.

Check node (node (node leaf 2 leaf) 5 (node leaf 7 leaf)) 10 (node (node leaf 12 leaf) 16 (node leaf 17 leaf)).

(* 
  Before we define the predicate we need some helper functions in
  order to establish the validity of the binary search tree properties.
*)
Fixpoint bst_left (N : nat) (T : tree) : Prop :=
  match T with
    | leaf => True
    | node l n r => (bst_left n l) /\ (N > n) /\ (bst_right n r)
  end.

Fixpoint bst_right (N : nat) (T : tree) : Prop :=
  match T with
    | leaf => True
    | node l n r => (N < n) /\ (N = n)
  end.

Fixpoint bst_prop (N : nat) (T : tree) : Prop :=
  match T with
    | leaf => True
    | node l n r => (bst_left
  end.

Check greater 4 leaf.

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
  | node l n r => (bst_left n l) \/ ()  bst_left n l /\ bst l /\ (greater n (bst l)) /\ (smaller_or_equal n (bst r))
  end.