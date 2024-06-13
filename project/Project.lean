import Mathlib
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

open BigOperators

-- 1. SMALL TASK
-- Formalize the recursive definition
-- C_0 = 0 and C_{n+1} = ∑_i=0^n C_i C_{n-i}
-- of the catalan numbers.
def catalan_number: ℕ → ℕ
| 0 => 1
| n+1 => ∑ i : Fin (n+1), (catalan_number i) * (catalan_number (n-i))

-- 2. SMALL TASK
-- Formalize the concept of plane trees.
inductive plane_tree : Type
| node : List plane_tree → plane_tree


-- 3. SMALL TASK
-- Formalize the concept of full binary trees.
inductive full_binary_tree: Type
| leaf : full_binary_tree
| node₂ : (T1 T2 : full_binary_tree) → full_binary_tree

-- 4. SMALL TASK
-- Construct the type of full binary trees with n nodes, not counting the leaves.
inductive binary_tree_with_nodes : (n : ℕ) → Type
| leaf : binary_tree_with_nodes 0
| node₁ : {n : ℕ} → binary_tree_with_nodes n → binary_tree_with_nodes (n + 1)
| node₂ : {m n : ℕ} → binary_tree_with_nodes m → binary_tree_with_nodes n → binary_tree_with_nodes (m + n + 1)

-- 5. SMALL TASK
-- Define the type of ballot sequences of length n.
inductive ballot_sequence : ℕ → ℕ → Type
| empty : ballot_sequence 0 0
| add_zero : {zeros ones : ℕ} → ballot_sequence zeros ones → ballot_sequence (zeros + 1) ones
| add_one : {zeros ones : ℕ} → ballot_sequence zeros ones → zeros > ones → ballot_sequence zeros (ones + 1)

-- 4. LARGE TASK
-- Construct a bijection
-- list PlaneTree ∼= PlaneTree
def list_plane_tree_of_plane_tree : plane_tree → List plane_tree
| .node l => l

def plane_tree_of_list_plane_tree : List plane_tree → plane_tree
| l => .node l

theorem plane_tree_isomorphic_to_list_plane_tree :
∀ (T : plane_tree),
T = plane_tree_of_list_plane_tree (list_plane_tree_of_plane_tree T) := by
intro T
cases T
simp[list_plane_tree_of_plane_tree]
simp[plane_tree_of_list_plane_tree]

theorem list_plane_tree_isomorphic_to_plane_tree :
∀ (T : List plane_tree),
T = list_plane_tree_of_plane_tree (plane_tree_of_list_plane_tree T) := by
intro T
simp[plane_tree_of_list_plane_tree, list_plane_tree_of_plane_tree]

-- 5. LARGE TASK
-- Construct the rotating isomorphism, which is the isomorphism between plane trees and full binary trees.

def plane_tree_of_full_binary_tree : full_binary_tree → plane_tree
| .leaf => .node []
| .node₂ T1 T2 => .node (plane_tree_of_full_binary_tree T1 :: list_plane_tree_of_plane_tree (plane_tree_of_full_binary_tree T2))

def full_binary_tree_of_plane_tree : plane_tree → full_binary_tree
  | .node [] => .leaf
  | .node (t1::ts) => .node₂ (full_binary_tree_of_plane_tree t1) (full_binary_tree_of_plane_tree (.node ts))

theorem plane_tree_isomorphic_to_full_binary_tree :
∀ (T : plane_tree), T = plane_tree_of_full_binary_tree (full_binary_tree_of_plane_tree T) := by
rintro ⟨⟨⟩ | ⟨T , l⟩⟩
· rfl
· rw[full_binary_tree_of_plane_tree]
  simp[plane_tree_of_full_binary_tree]
  apply And.intro
  rw[<-plane_tree_isomorphic_to_full_binary_tree]
  rw[<-plane_tree_isomorphic_to_full_binary_tree]
  rw[list_plane_tree_of_plane_tree]

theorem full_binary_tree_isomorphic_to_plane_tree :
∀ (T : full_binary_tree),
T = full_binary_tree_of_plane_tree (plane_tree_of_full_binary_tree T) := by
intro T
induction T with
| leaf =>
  simp[plane_tree_of_full_binary_tree, full_binary_tree_of_plane_tree]
| node₂ T1 T2 HT1 HT2 =>
  simp[plane_tree_of_full_binary_tree, full_binary_tree_of_plane_tree]
  apply And.intro
  rw[<-HT1]
  simp[list_plane_tree_of_plane_tree]
  split
  · case node₂ type h =>
    rw[<- h]
    rw[<- HT2]
