-- This module serves as the root of the `Project` library.
-- Import modules here that should be built as part of the library.
import «Project».Basic
import Mathlib

/- The type of binary trees -/

inductive binary_tree : Type
| leaf : binary_tree
| node₁ : binary_tree → binary_tree
| node₂ : binary_tree → binary_tree → binary_tree


/- The height of a binary tree -/

def binary_tree.height : binary_tree → ℕ
| .leaf => 1
| .node₁ T => T.height + 1
| .node₂ T1 T2 => max T1.height T2.height + 1


/- The number of nodes (including leaves) of a binary tree -/

def binary_tree.number_of_nodes : binary_tree → ℕ
| .leaf => 1
| .node₁ T => T.number_of_nodes + 1
| .node₂ T1 T2 => T1.number_of_nodes + T2.number_of_nodes + 1


/- The type of full binary tree -/

inductive full_binary_tree: Type
| leaf : full_binary_tree
| node₂ : (T1 T2 : full_binary_tree) → full_binary_tree


/- The height of a full binary tree -/

def full_binary_tree.height : full_binary_tree → ℕ
| .leaf => 1
| .node₂ T1 T2 => max T1.height T2.height + 1


/- The number of nodes including leaves of a full binary tree -/

def full_binary_tree.number_of_nodes : full_binary_tree → ℕ
| .leaf => 1
| .node₂ T1 T2 => T1.number_of_nodes + T2.number_of_nodes + 1


/- Function that converts full binary tree to binary tree -/

def binary_tree_of_full_binary_tree : full_binary_tree → binary_tree
| .leaf => .leaf -- pika se navezuje na prvi argument (oba imata konstruktor leaf)
| .node₂ T1 T2 => .node₂ (binary_tree_of_full_binary_tree T1) (binary_tree_of_full_binary_tree T2)

theorem eq_height_binary_tree_of_full_binary_tree :
(T : full_binary_tree) → T.height = (binary_tree_of_full_binary_tree T).height := by -- by pomeni da začnemo dokaz
intro T
induction T with
| leaf => rfl
| node₂ T1 T2 HT1 HT2 =>
  simp [full_binary_tree.height, binary_tree.height] -- simp je unfoldu definition height
  rw[HT1, HT2]

theorem eq_number_of_nodes_binary_tree_of_full_binary_tree :
(T : full_binary_tree) → T.number_of_nodes = (binary_tree_of_full_binary_tree T).number_of_nodes := by
intro T
induction T with
| leaf => rfl
| node₂ T1 T2 HT1 HT2 =>
  simp[full_binary_tree.number_of_nodes, binary_tree.number_of_nodes]
  rw[HT1, HT2]

inductive binary_tree_with_nodes : (n : ℕ) → Type
| leaf : binary_tree_with_nodes 1
| node₁ : {n : ℕ} → binary_tree_with_nodes n → binary_tree_with_nodes (n + 1)
| node₂ : {m n : ℕ} → binary_tree_with_nodes m → binary_tree_with_nodes n → binary_tree_with_nodes (m + n)


/- The type of vectors of elements in a type A (aka labeled unary trees) -/

inductive vector (A : Type) : (n : ℕ) → Type -- A parameter (se ne spreminja), n argument (se spreminja)
| nil : vector A 0
| cons : (n : ℕ) → A → vector A n → vector A (n + 1)


/- A function converting binary trees with n nodes to ordinary binary trees -/

def binary_tree_of_binary_tree_with_nodes {n : ℕ} : binary_tree_with_nodes n → binary_tree
| .leaf => .leaf
| .node₁ T => .node₁ (binary_tree_of_binary_tree_with_nodes T)
| .node₂ T1 T2 => .node₂ (binary_tree_of_binary_tree_with_nodes T1) (binary_tree_of_binary_tree_with_nodes T2)

theorem eq_number_of_nodes_binary_tree_of_full_binary_tree_with_nodes :
∀ (n : ℕ)
 (T : binary_tree_with_nodes n), n = (binary_tree_of_binary_tree_with_nodes T).number_of_nodes := by
  intros n T
  induction T with
  | leaf => rfl
  | node_1 T HT1 =>
    simp [binary_tree.number_of_nodes]
    exact HT1
  | node_2 T1 T2 HT1 HT2 =>
    simp [binary_tree.number_of_nodes]
    rw [<- HT1, <- HT2]
