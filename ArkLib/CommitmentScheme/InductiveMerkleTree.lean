/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import VCVio
import ArkLib.Data.Math.Basic
import ArkLib.CommitmentScheme.Basic
import Mathlib.Data.Vector.Snoc

/-!
# Inductive Merkle Trees

This file implements Merkle Trees. In contrast to the other Merkle tree implementation in
`ArkLib.CommitmentScheme.MerkleTree`, this one is defined inductively.

## Notes & TODOs

### Binary Tree API

- Split this BinaryTree API to a new file
- More API about equivlances between
  - `SkeletonNodeIndex` ≃ `SkeletonInternalIndex` ⊕ `SkeletonLeafIndex`
  - analogously
  - `FullDataTree α ≃ InternalDataTree α × LeafDataTree α`
  - OR EVEN BETTER:
    - Redefine `FullDataTree`, `InternalDataTree`, `LeafDataTree` in terms of functions from `Skeleton`, so that this equivalence follows immediately from the above by algebra.
- Replace `List`s with `FreeSubgroup` for ancestors?
- Functions for navigating tree
  - [ ] Go to parent if it exists
  - [ ] Go to left child if it exists
  - [ ] Go to right child if it exists
  - [ ] Go to sibling if it exists
  - [ ] Return Sym2 of left and right children
  - Function for relationships between all these tree navigations
    - [ ] How do these navigations affect depth?
    - [ ] Which navigation sequences are equivalent to each other?
- API for functorial mapping over data carried by the tree
- API for flatttening a tree to a list
- Define `Lattice` strutcure of trees
  - a susbset relation on trees, mappings of indices to indices of supertrees
- Define a datatype for indices of general trees, equivalent to lists of bools, and relationships to normal types.

### More Things needed for basic Merkle Trees

- Collision Lemma (See SNARGs book 18.3)
  - (this is really not a lemma about oracles, so it could go with the binary tree API)

### More Complicated Merkle Trees

We want this treatment to be as comprehensive as possible. In particular, our formalization
should (eventually) include all complexities such as the following:

- Multi-instance extraction & simulation
- Dealing with arbitrary trees (may have arity > 2, or is not complete)
- Path pruning optimization for multi-leaf proofs



-/

namespace BinaryTree
#check Lattice

/-!
# Binary Trees

This section contains datatypes for working with binary trees.

There

-/

/--
Inductive data type for a binary tree skeleton.
A skeleton is a binary tree without values, used to represent the structure of the tree.
-/
inductive Skeleton where
  | leaf : Skeleton
  | internal : Skeleton → Skeleton → Skeleton

/-- Type of indices of leaves of a skeleton -/
inductive SkeletonLeafIndex : Skeleton → Type
  | ofLeaf : SkeletonLeafIndex Skeleton.leaf
  | ofLeft {left right : Skeleton} (idxLeft : SkeletonLeafIndex left) :
      SkeletonLeafIndex (Skeleton.internal left right)
  | ofRight {left right : Skeleton} (idxRight : SkeletonLeafIndex right) :
      SkeletonLeafIndex (Skeleton.internal left right)

/-- Type of indices of any node of a skeleton -/
inductive SkeletonNodeIndex : Skeleton → Type
  | ofLeaf : SkeletonNodeIndex Skeleton.leaf
  | ofInternal {left right} :
      SkeletonNodeIndex (Skeleton.internal left right)
  | ofLeft {left right : Skeleton} (idxLeft : SkeletonNodeIndex left) :
      SkeletonNodeIndex (Skeleton.internal left right)
  | ofRight {left right : Skeleton} (idxRight : SkeletonNodeIndex right) :
      SkeletonNodeIndex (Skeleton.internal left right)

/-- Construct a `SkeletonLeafIndex` from a `SkeletonNodeIndex` -/
def SkeletonLeafIndex.toNodeIndex {s : Skeleton} (idx : SkeletonLeafIndex s) :
    SkeletonNodeIndex s :=
  match idx with
  | SkeletonLeafIndex.ofLeaf => SkeletonNodeIndex.ofLeaf
  | SkeletonLeafIndex.ofLeft idxLeft =>
    SkeletonNodeIndex.ofLeft (SkeletonLeafIndex.toNodeIndex idxLeft)
  | SkeletonLeafIndex.ofRight idxRight =>
    SkeletonNodeIndex.ofRight (SkeletonLeafIndex.toNodeIndex idxRight)

/-- Depth of a SkeletonNodeIndex -/
def SkeletonNodeIndex.depth {s : Skeleton} : SkeletonNodeIndex s → Nat
  | SkeletonNodeIndex.ofLeaf => 0
  | SkeletonNodeIndex.ofInternal => 0
  | SkeletonNodeIndex.ofLeft idxLeft => idxLeft.depth + 1
  | SkeletonNodeIndex.ofRight idxRight => idxRight.depth + 1

def SkeletonNodeIndex.parent {s : Skeleton} (idx : SkeletonNodeIndex s) : Option (SkeletonNodeIndex s) :=
  match idx with
  | SkeletonNodeIndex.ofLeaf => none
  | SkeletonNodeIndex.ofInternal => none
  | SkeletonNodeIndex.ofLeft (.ofLeaf) => some .ofInternal
  | SkeletonNodeIndex.ofLeft (.ofInternal) => some .ofInternal
  | SkeletonNodeIndex.ofLeft idxLeft =>
    idxLeft.parent.map (SkeletonNodeIndex.ofLeft)
  | SkeletonNodeIndex.ofRight (.ofLeaf) => some .ofInternal
  | SkeletonNodeIndex.ofRight (.ofInternal) => some .ofInternal
  | SkeletonNodeIndex.ofRight idxRight =>
    idxRight.parent.map (SkeletonNodeIndex.ofRight)

/-- Get the root value of a InternalDataTree. -/
def getRootIndex (s : Skeleton) : SkeletonNodeIndex s := match s with
  | Skeleton.leaf => SkeletonNodeIndex.ofLeaf
  | Skeleton.internal left right =>
    SkeletonNodeIndex.ofInternal

-- Analogous to `Cache`
/--
A binary tree with values stored in internal nodes.
-/
inductive InternalDataTree (α : Type) : Skeleton → Type
  | leaf : InternalDataTree α Skeleton.leaf
  | internal {left right} (value : α)
      (leftData : InternalDataTree α left)
      (rightData : InternalDataTree α right) : InternalDataTree α (Skeleton.internal left right)
  deriving Repr

/--
A binary tree with values stored at leaves.
-/
inductive LeafDataTree (α : Type) : Skeleton → Type
  | leaf (value : α) : LeafDataTree α Skeleton.leaf
  | internal {left right} (leftData : LeafDataTree α left) (rightData : LeafDataTree α right) :
      LeafDataTree α (Skeleton.internal left right)
  deriving Repr

/-- Get the root value of a InternalDataTree. -/
def LeafDataTree.getValueAtIndex {s} {α : Type} (tree : LeafDataTree α s) (idx : SkeletonLeafIndex s) : α :=
  match tree, idx with
  | LeafDataTree.leaf value, SkeletonLeafIndex.ofLeaf => value
  | LeafDataTree.internal left right, SkeletonLeafIndex.ofLeft idxLeft =>
    LeafDataTree.getValueAtIndex left idxLeft
  | LeafDataTree.internal left right, SkeletonLeafIndex.ofRight idxRight =>
    LeafDataTree.getValueAtIndex right idxRight

/--
A binary tree with values stored at both leaves and internal nodes.
-/
inductive FullDataTree (α : Type) : Skeleton → Type
  | leaf (value : α) : FullDataTree α Skeleton.leaf
  | internal {left right} (value : α)
      (leftData : FullDataTree α left)
      (rightData : FullDataTree α right) :
      FullDataTree α (Skeleton.internal left right)

/-- Get the root value of a InternalDataTree. -/
def FullDataTree.getValueAtIndex {s} {α : Type} (tree : FullDataTree α s) (idx : SkeletonNodeIndex s) : α :=
  match tree, idx with
  | FullDataTree.leaf value, SkeletonNodeIndex.ofLeaf => value
  | FullDataTree.internal value _ _, SkeletonNodeIndex.ofInternal => value
  | FullDataTree.internal _ left right, SkeletonNodeIndex.ofLeft idxLeft =>
    FullDataTree.getValueAtIndex left idxLeft
  | FullDataTree.internal _ left right, SkeletonNodeIndex.ofRight idxRight =>
    FullDataTree.getValueAtIndex right idxRight


/-- Get the root value of a InternalDataTree. -/
def FullDataTree.getRootValue {s} {α : Type} (tree : FullDataTree α s) :=
  tree.getValueAtIndex (getRootIndex s)


lemma SkeletonNodeIndex.parent_of_depth_zero {s : Skeleton} (idx : SkeletonNodeIndex s) (h : idx.depth = 0) :
    parent idx = none := by
  cases idx with
  | ofLeaf => rfl
  | ofInternal => rfl
  | ofLeft idxLeft =>
    unfold depth at h
    simp_all
  | ofRight idxRight =>
    unfold depth at h
    simp_all



lemma SkeletonNodeIndex.parent_of_depth_succ {s : Skeleton} (idx : SkeletonNodeIndex s) (n : ℕ) (h : idx.depth = n + 1) :
    idx.parent.map depth = some n := by
  sorry
  -- cases idx with
  -- | ofLeaf =>
  --   unfold depth at h
  --   exfalso
  --   omega
  -- | ofInternal =>
  --   unfold depth at h
  --   exfalso
  --   omega
  -- | ofLeft idxLeft =>
  --   cases idxLeft with
  --   | ofLeaf =>
  --     unfold depth at h
  --     unfold depth at h
  --     unfold parent
  --     unfold Option.map
  --     unfold depth
  --     simp_all
  --   | ofInternal =>
  --     unfold depth at h
  --     unfold depth at h
  --     unfold parent
  --     unfold Option.map
  --     unfold depth
  --     simp_all
  --   | ofLeft idxLeftLeft =>
  --     unfold depth at h
  --     unfold depth at h
  --     unfold parent
  --     rw [Option.map_map]
  --     unfold Option.map
  --     cases idxLeftLeft.ofLeft.parent with
  --     | none =>
  --       simp_all
  --       sorry
  --     | some idxLeftLeftParent =>
  --       sorry
  --     -- unfold depth
  --     simp_all
  --   | ofRight idxLeftRight => sorry
  -- | ofRight idxRight => sorry


/--
Given a `Skeleton`, and a node index of the skeleton,
return a list of node indices which are the ancestors of the node, starting with the root node, working down to the node itself.
-/
def SkeletonNodeIndex.findAncestors {s : Skeleton} (idx : SkeletonNodeIndex s) : List (SkeletonNodeIndex s) :=
  match idx with
  | SkeletonNodeIndex.ofLeaf => [SkeletonNodeIndex.ofLeaf]
  | SkeletonNodeIndex.ofInternal => [SkeletonNodeIndex.ofInternal]
  | SkeletonNodeIndex.ofLeft idxLeft =>
    .ofInternal :: ((idxLeft.findAncestors)).map (SkeletonNodeIndex.ofLeft)
  | SkeletonNodeIndex.ofRight idxRight =>
    .ofInternal :: ((idxRight.findAncestors)).map (SkeletonNodeIndex.ofRight)

/--
Given a `Skeleton`, and a leaf index of the skeleton, return a list of node indices which are the ancestors of the leaf.
-/
def findAncestors {s : Skeleton} (idx : SkeletonLeafIndex s) : List (SkeletonNodeIndex s) :=
  SkeletonNodeIndex.findAncestors idx.toNodeIndex

/--
Return the sibling node index of a given `SkeletonNodeIndex`. Or `none` if the node is the root
-/
def SkeletonNodeIndex.findSibling {s : Skeleton} (idx : SkeletonNodeIndex s) : Option (SkeletonNodeIndex s) :=
  match idx with
  | SkeletonNodeIndex.ofLeaf => none
  | SkeletonNodeIndex.ofInternal => none
  | @SkeletonNodeIndex.ofLeft left right idxLeft =>
    match idxLeft with
    | SkeletonNodeIndex.ofLeaf => some (getRootIndex right).ofRight
    | SkeletonNodeIndex.ofInternal => some (getRootIndex right).ofRight
    | SkeletonNodeIndex.ofLeft idxLeftLeft =>
      idxLeftLeft.ofLeft.findSibling.map (SkeletonNodeIndex.ofLeft)
    | SkeletonNodeIndex.ofRight idxLeftRight =>
      idxLeftRight.ofRight.findSibling.map (SkeletonNodeIndex.ofLeft)
  | @SkeletonNodeIndex.ofRight left right idxRight =>
    match idxRight with
    | SkeletonNodeIndex.ofLeaf => some (getRootIndex left).ofLeft
    | SkeletonNodeIndex.ofInternal => some (getRootIndex left).ofLeft
    | SkeletonNodeIndex.ofLeft idxRightLeft =>
      idxRightLeft.ofLeft.findSibling.map (SkeletonNodeIndex.ofRight)
    | SkeletonNodeIndex.ofRight idxRightRight =>
      idxRightRight.ofRight.findSibling.map (SkeletonNodeIndex.ofRight)

/-- Find the siblings of the ancestors of a node -/
def SkeletonNodeIndex.findUncles {s : Skeleton} (idx : SkeletonNodeIndex s) :
    List (SkeletonNodeIndex s) := (idx.findAncestors.filterMap (fun idx => idx.findSibling))


end BinaryTree

namespace InductiveMerkleTree

open List OracleSpec OracleComp BinaryTree

variable (α : Type)

/-- Define the domain & range of the (single) oracle needed for constructing a Merkle tree with
    elements from some type `α`.

  We may instantiate `α` with `BitVec n` or `Fin (2 ^ n)` to construct a Merkle tree for boolean
  vectors of length `n`. -/
@[reducible]
def spec : OracleSpec Unit := fun _ => (α × α, α)

@[simp]
lemma domain_def : (spec α).domain () = (α × α) := rfl

@[simp]
lemma range_def : (spec α).range () = α := rfl

section

variable [DecidableEq α] [Inhabited α] [Fintype α]

/-- Example: a single hash computation -/
def singleHash (left : α) (right : α) : OracleComp (spec α) α := do
  let out ← query (spec := spec α) () ⟨left, right⟩
  return out

variable {α : Type}


-- /-- Find the path from root to a leaf with the given value. -/
-- def findPath [DecidableEq α] (a : α) : BinaryTree α → Option (List Bool)
--   | BinaryTree.nil => none
--   | BinaryTree.node _ left right =>
--     match findPath a left with
--     | some path => some (false :: path)
--     | none =>
--       match findPath a right with
--       | some path => some (true :: path)
--       | none => none

-- /-- Helper function to get the proof for a value at a given path. -/
-- def getProofHelper [DecidableEq α] : List Bool → BinaryTree α → List α
--   | _, BinaryTree.nil => []
--   | _, BinaryTree.leaf _ => []
--   | [], BinaryTree.node _ _ _ => []
--   | false :: rest, BinaryTree.node _ l r =>
--     match getRoot r with
--     | none => getProofHelper rest l
--     | some v => v :: getProofHelper rest l
--   | true :: rest, BinaryTree.node _ l r =>
--     match getRoot l with
--     | none => getProofHelper rest r
--     | some v => v :: getProofHelper rest r

def buildMerkleTree_with_hash {s} (leaf_tree : LeafDataTree α s) (hashFn : α → α → α) : (FullDataTree α s) :=
  match leaf_tree with
  | LeafDataTree.leaf a => FullDataTree.leaf a
  | LeafDataTree.internal left right =>
    let leftTree := buildMerkleTree_with_hash left hashFn
    let rightTree := buildMerkleTree_with_hash right hashFn
    let rootHash := hashFn (leftTree.getRootValue) (rightTree.getRootValue)
    FullDataTree.internal rootHash leftTree rightTree

/-- Build the full Merkle tree, returning the cache -/
def buildMerkleTree {s} (leaf_tree : LeafDataTree α s) : OracleComp (spec α) (FullDataTree α s) :=
  match leaf_tree with
  | LeafDataTree.leaf a => do return (FullDataTree.leaf a)
  | LeafDataTree.internal left right => do
    let leftTree ← buildMerkleTree left
    let rightTree ← buildMerkleTree right
    let rootHash ← singleHash α leftTree.getRootValue rightTree.getRootValue
    return FullDataTree.internal rootHash leftTree rightTree

/-- Generate a Merkle proof for a leaf at a given idx
    The proof consists of the sibling hashes needed to recompute the root.

-/
def generateProof {s} (cache_tree : FullDataTree α s) (idx : BinaryTree.SkeletonLeafIndex s) : List α :=
  (idx.toNodeIndex.findUncles.map (fun siblingIdx =>
    cache_tree.getValueAtIndex siblingIdx))

/--
Given a leaf index, a leaf value at that index, and putative proof,
returns the hash that would be the root of the tree if the proof was valid.
i.e. the hash obtained by combining the leaf in sequence with each member of the proof,
according to its index.
-- TODO should this, instead of a List, take a Vector of length idx.depth?
-/
def getPutativeRoot {s} (idx : BinaryTree.SkeletonLeafIndex s) (leafValue : α)
    (proof : List α) : OracleComp (spec α) α :=
  match proof with
  | [] => return leafValue -- If no proof, the root is just the leaf value
  | siblingBelowRootHash :: restProof => do
    match idx with
    | BinaryTree.SkeletonLeafIndex.ofLeaf =>
      -- This indicates that the proof is longer than the depth of the tree, which is invalid.
      -- A more well-typed version using `Vector` might prevent this.
      -- FOr now, we just return the leaf value.
      return leafValue
    | BinaryTree.SkeletonLeafIndex.ofLeft idxLeft =>
      -- Recursively get the hash of the ancestor of the leaf which is just below the root
      let ancestorBelowRootHash ← getPutativeRoot idxLeft leafValue restProof
      singleHash α ancestorBelowRootHash siblingBelowRootHash
    | BinaryTree.SkeletonLeafIndex.ofRight idxRight =>
      -- Recursively get the hash of the ancestor of the leaf which is just below the root
      let ancestorBelowRootHash ← getPutativeRoot idxRight leafValue restProof
      singleHash α siblingBelowRootHash ancestorBelowRootHash

/-- Verify a Merkle proof `proof` that a given `leaf` at index `i` is in the Merkle tree with given
  `root`.
  Works by computing the putative root based on the branch, and comparing that to the actual root.
  Outputs `failure` if the proof is invalid. -/
def verifyProof [DecidableEq α] {s} (idx : BinaryTree.SkeletonLeafIndex s) (leafValue : α) (rootValue : α)
    (proof : List α) : OracleComp (spec α) Unit := do
  let putative_root ← getPutativeRoot idx leafValue proof
  guard (putative_root = rootValue)

theorem singleHash_neverFails [DecidableEq α] [inst_1 : SelectableType α] (left right : α)
    (preexisting_cache : (spec α).QueryCache) :
    ((simulateQ randomOracle (singleHash α left right)).run preexisting_cache).neverFails := by
  unfold singleHash
  simp only [range_def, bind_pure, simulateQ_query,
    unifOracle.apply_eq, StateT.run_bind, StateT.run_get, pure_bind]
  simp
  cases preexisting_cache () (left, right) with
  | none =>
    simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, bind_pure_comp,
      StateT.run_modifyGet, Functor.map_map, neverFails_map_iff, neverFails_uniformOfFintype]
  | some u =>
    simp only [StateT.run_pure, neverFails_pure]

theorem buildMerkleTree_neverFails {α : Type} [inst : DecidableEq α] [inst_1 : SelectableType α] {s : Skeleton}
    (leaf_tree : LeafDataTree α s) (preexisting_cache : (spec α).QueryCache) :
    ((simulateQ randomOracle (buildMerkleTree leaf_tree)).run preexisting_cache).neverFails := by
  induction leaf_tree generalizing preexisting_cache with
  | leaf a =>
    unfold buildMerkleTree
    simp only [simulateQ_pure, StateT.run_pure, neverFails_pure]
  | internal left right left_ih right_ih =>
    unfold buildMerkleTree
    simp [simulateQ_bind, StateT.run_bind, neverFails_bind_iff, left_ih, right_ih]
    intro merkle_cache_left query_cache h_mem_support merkle_cache_right query_cache' h_mem_support'
    clear left_ih right_ih
    exact
      singleHash_neverFails merkle_cache_left.getRootValue merkle_cache_right.getRootValue
        query_cache'

theorem completeness [DecidableEq α] [SelectableType α] {s} (leaf_tree : LeafDataTree α s) (idx : BinaryTree.SkeletonLeafIndex s)
    (preexisting_cache : (spec α).QueryCache) :
    (((do
      let cache ← buildMerkleTree leaf_tree
      let proof := generateProof cache idx
      let verif ← verifyProof idx (leaf_tree.getValueAtIndex idx) (cache.getRootValue) proof).simulateQ
      (randomOracle)).run preexisting_cache).neverFails := by
  simp [neverFails_bind_iff]
  constructor
  · -- buildMerkleTree never fails
    exact buildMerkleTree_neverFails leaf_tree preexisting_cache
  · -- verifyProof never fails on the output of generateProof after buildMerkleTree
    intros merkle_tree_cache query_cache h_mem_support
    -- Need a theorem to characterize
    -- `(merkle_tree_cache, query_cache) ∈ ((simulateQ randomOracle (buildMerkleTree leaf_tree)).run preexisting_cache).support`
    -- i.e. this is equivalent to:
    --  - All merkle_tree_cache parent-child relationships are in the query_cache
    --  - Everything in the preexisting_cache is in the query_cache (so merkle_tree_cache and preexisting_cache are compatible)
    --  - Nothing else is in the query_cache
    simp [verifyProof, neverFails_bind_iff]
    constructor
    · -- getPutativeRoot never fails
      sorry
    · -- guard never fails
      intro putative_root query_cache' h_mem_support'
      -- Now, Need a theorem to characterize
      -- `(putative_root, query_cache') ∈ ((simulateQ randomOracle
      --     (getPutativeRoot idx (leaf_tree.getValueAtIndex idx) (generateProof merkle_tree_cache idx))).run
      -- query_cache✝).support`

      sorry
