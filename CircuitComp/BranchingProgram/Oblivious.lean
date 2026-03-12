import CircuitComp.BranchingProgram.Basic

/-!

Every branching program can be converted to an oblivious branching program
(`LayeredBranchingProgram.IsOblivious`).

First we show that a `SkipBranchingProgram` can be converted to an oblivious branching program,
without increasing width (but with an increase in depth). Then we show that we can convert
this back to a LayeredBranchingProgram without increasing width, and while keeping it oblivious.
-/

noncomputable section

namespace SkipBranchingProgram

variable {α : Type u} {β : Type v} {γ : Type w} [Fintype α] (P : SkipBranchingProgram α β γ)

theorem toLayered_width [P.Finite] : P.toLayered.width = P.width := by
  admit

theorem toLayered_IsOblivious (h : P.IsOblivious) : P.toLayered.IsOblivious := by
  admit

namespace toOblivious

/-- Node type at depth `t` in `SkipBranchingProgram.toOblivious`. -/
def ObliviousNodes (t : Fin (P.depth * Fintype.card α + 1)) : Type v :=
  let k := Fintype.card α
  let E := Fintype.equivFin α
  if h : t < P.depth * k then
    let i : Fin P.depth := ⟨t / k, Nat.div_lt_of_lt_mul <| by linarith⟩
    let j : Fin k := ⟨t % k, Nat.mod_lt _ <| by contrapose! h; simp_all⟩
    { u : P.nodes i.castSucc // E (P.nodeVar u) ≥ j }
  else
    P.nodes (Fin.last P.depth)

/-- Variables read at depth `t` in `SkipBranchingProgram.toOblivious`. -/
def ObliviousNodeVar (t : Fin (P.depth * Fintype.card α)) : α :=
  (Fintype.equivFin α).symm ⟨t % Fintype.card α,
    Nat.mod_lt _ (Nat.pos_of_mul_pos_left (Fin.pos t))⟩

/-- Unfolding lemma for `ObliviousNodes` at non-last positions. -/
lemma obliviousNodes_unfold (t : Fin (P.depth * Fintype.card α + 1))
    (ht : (t : ℕ) < P.depth * Fintype.card α)
    (hk : 0 < Fintype.card α) :
    ObliviousNodes P t =
    { w : P.nodes (⟨(t : ℕ) / Fintype.card α,
        Nat.div_lt_of_lt_mul (by linarith)⟩ : Fin P.depth).castSucc //
      (Fintype.equivFin α) (P.nodeVar w) ≥
        (⟨(t : ℕ) % Fintype.card α,
          Nat.mod_lt _ hk⟩ : Fin (Fintype.card α)) } := by
  simp only [ObliviousNodes, dif_pos ht]

/-- The edge function for the oblivious branching program.
If the node's variable index equals `t % k`, take the original edge and jump to `m * k`.
Otherwise, pass through to `t + 1`. -/
def obliviousEdge (t : Fin (P.depth * Fintype.card α))
  (u : ObliviousNodes P t.castSucc) (b : β) :
      (m : Fin (P.depth * Fintype.card α + 1)) × ObliviousNodes P m := by
  have hk_pos : 0 < Fintype.card α := Nat.pos_of_mul_pos_left (Fin.pos t)
  have ht_lt : (t : ℕ) < P.depth * Fintype.card α := t.isLt
  have hobs := obliviousNodes_unfold P t.castSucc ht_lt hk_pos
  set i : Fin P.depth := ⟨(t : ℕ) / Fintype.card α, Nat.div_lt_of_lt_mul (by linarith)⟩
  set j : Fin (Fintype.card α) := ⟨(t : ℕ) % Fintype.card α, Nat.mod_lt _ hk_pos⟩
  set u' : { w : P.nodes i.castSucc // (Fintype.equivFin α) (P.nodeVar w) ≥ j } :=
    cast hobs u with hu'
  by_cases hvar : (Fintype.equivFin α) (P.nodeVar u'.1) = j
  · set next := P.edges u'.1 b
    set m := next.1; set v := next.2
    have hm_bound : (m : ℕ) * Fintype.card α < P.depth * Fintype.card α + 1 :=
      Nat.lt_succ_of_le (Nat.mul_le_mul_right _ (Nat.le_of_lt_succ m.isLt))
    by_cases hml : (m : ℕ) * Fintype.card α < P.depth * Fintype.card α
    · refine ⟨⟨m * Fintype.card α, hm_bound⟩, ?_⟩
      rw [obliviousNodes_unfold P _ hml hk_pos]
      exact ⟨cast (by congr 1; exact Fin.ext (Nat.mul_div_cancel (m : ℕ) hk_pos).symm) v,
             by simp [Fin.le_iff_val_le_val]⟩
    · have hm_eq : (m : ℕ) = P.depth := by have := m.isLt; nlinarith
      refine ⟨⟨P.depth * Fintype.card α, Nat.lt_succ_self _⟩, ?_⟩
      show ObliviousNodes P ⟨P.depth * Fintype.card α, _⟩
      simp only [ObliviousNodes,
        dif_neg (show ¬ (P.depth * Fintype.card α < P.depth * Fintype.card α) from Nat.lt_irrefl _)]
      exact cast (by congr 1; exact Fin.ext (by simp [Fin.last]; omega)) v
  · have hgt : (Fintype.equivFin α) (P.nodeVar u'.1) > j := lt_of_le_of_ne u'.2 (Ne.symm hvar)
    have hj_lt : (j : ℕ) < Fintype.card α - 1 := by
      have := ((Fintype.equivFin α) (P.nodeVar u'.1)).isLt; omega
    have ht1_lt : (t : ℕ) + 1 < P.depth * Fintype.card α := by
      calc (t : ℕ) + 1
          = Fintype.card α * ((t : ℕ) / Fintype.card α) + ((t : ℕ) % Fintype.card α + 1) := by
              linarith [Nat.div_add_mod (t : ℕ) (Fintype.card α)]
        _ ≤ Fintype.card α * ((t : ℕ) / Fintype.card α) + (Fintype.card α - 1) := by
              have hj_val : (j : ℕ) = (t : ℕ) % Fintype.card α := rfl; omega
        _ < Fintype.card α * ((t : ℕ) / Fintype.card α + 1) := by
              rw [Nat.mul_add, Nat.mul_one]; omega
        _ ≤ Fintype.card α * P.depth := Nat.mul_le_mul_left _ i.isLt
        _ = P.depth * Fintype.card α := by ring
    have h_div : ((t : ℕ) + 1) / Fintype.card α = (t : ℕ) / Fintype.card α := by
      rw [show (t : ℕ) + 1 = (t : ℕ) % Fintype.card α + 1 +
            (t : ℕ) / Fintype.card α * Fintype.card α from
            by linarith [Nat.div_add_mod (t : ℕ) (Fintype.card α)],
          Nat.add_mul_div_right _ _ hk_pos,
          Nat.div_eq_of_lt (by have : (j : ℕ) = (t : ℕ) % Fintype.card α := rfl; omega),
          Nat.zero_add]
    have h_mod : ((t : ℕ) + 1) % Fintype.card α = (t : ℕ) % Fintype.card α + 1 := by
      rw [show (t : ℕ) + 1 = (t : ℕ) % Fintype.card α + 1 +
            (t : ℕ) / Fintype.card α * Fintype.card α from
            by linarith [Nat.div_add_mod (t : ℕ) (Fintype.card α)],
          Nat.add_mul_mod_self_right,
          Nat.mod_eq_of_lt (by have : (j : ℕ) = (t : ℕ) % Fintype.card α := rfl; omega)]
    refine ⟨⟨(t : ℕ) + 1, Nat.lt_succ_of_lt ht1_lt⟩, ?_⟩
    rw [obliviousNodes_unfold P _ ht1_lt hk_pos]
    exact ⟨cast (by congr 1; exact Fin.ext h_div.symm) u'.1,
           by
             convert Nat.succ_le_of_lt hgt using 1;
             simp [Fin.le_iff_val_le_val, * ]
             grind⟩

/-
PROBLEM
The edge target is strictly above the source layer.
PROVIDED SOLUTION
Unfold `obliviousEdge` and examine both branches of `by_cases hvar`. In the match case (hvar is true), the target is `m * k` where `m` is from `P.edges u' b`, and `P.edges_layer_gt` gives `i.castSucc < m`, so `i * k + k ≤ m * k` while `t = i * k + j ≤ i * k + (k-1) < m * k`. In the pass-through case (hvar is false), the target is `t + 1 > t`.
-/
lemma obliviousEdge_fst_gt (t : Fin (P.depth * Fintype.card α))
    (u : ObliviousNodes P t.castSucc) (b : β) :
    t.castSucc < (obliviousEdge P t u b).1 := by
    -- By definition of `obliviousEdge`, the first component of the edge is either `m * k` or `t + 1`, both of which are greater than `t`.
  simp [obliviousEdge];
  split_ifs <;> norm_num [ Fin.lt_iff_val_lt_val ] at *;
  have := P.edges_layer_gt ( cast ( obliviousNodes_unfold P t.castSucc t.2 ( Nat.pos_of_mul_pos_left ( Fin.pos t ) ) ) u |>.1 ) b; simp_all +decide [ Fin.lt_iff_val_lt_val ] ;
  nlinarith [ Nat.div_add_mod t ( Fintype.card α ), Nat.mod_lt t ( Nat.pos_of_mul_pos_left ( Fin.pos t ) ) ]

/-
PROBLEM
The type `ObliviousNodes P 0` is a `Unique` type, inheriting from `P.startUnique`.
PROVIDED SOLUTION
Split on whether 0 < P.depth * Fintype.card α using by_cases. Case 1 (h : 0 < P.depth * Fintype.card α): After simp [ObliviousNodes, dif_pos h], the type becomes { w : P.nodes ⟨0, _⟩.castSucc // ... ≥ ⟨0, _⟩ } which is a subtype of P.nodes 0 with a trivially true condition. Since P.nodes 0 is Unique (from P.startUnique), every element has the form ⟨P.start, _⟩. Construct the Unique instance with default ⟨cast _ P.start, _⟩ and uniq using Subtype.ext and P.startUnique.uniq.  Case 2 (h : ¬ 0 < P.depth * Fintype.card α): After simp [ObliviousNodes, dif_neg h], the type is P.nodes (Fin.last P.depth). Since depth = 0 (from the condition), Fin.last 0 = 0, so this is P.nodes 0, which is Unique by P.startUnique.
Unfold ObliviousNodes. Use by_cases on (0 : ℕ) < P.depth * Fintype.card α. In the true case, simp [ObliviousNodes, dif_pos] to get { w : P.nodes 0 // E (nodeVar w) ≥ 0 }. The ≥ 0 condition is trivially true for all w. Since P.nodes 0 is Unique via P.startUnique, construct the Unique instance for the subtype: default is ⟨P.start, trivial⟩ and uniq uses Subtype.ext with P.startUnique.uniq. In the false case, depth = 0, so ObliviousNodes is P.nodes (Fin.last 0) = P.nodes 0, and use P.startUnique directly (possibly with a cast).
Use `simp only [ObliviousNodes]` then `split_ifs with h`. In the positive case (h : 0 < P.depth * Fintype.card α), the type becomes `{ u // ... ≥ ⟨0 % k, _⟩ }` which is a subtype of `P.nodes ⟨0/k, _⟩.castSucc`. Note `0/k = 0` and `⟨0, _⟩.castSucc` is definitionally 0, so the nodes type is `P.nodes 0` up to cast. The condition `≥ ⟨0%k, _⟩ = ≥ ⟨0, _⟩` is trivially true. Construct the Unique via `Unique.mk'` or directly: default is `⟨cast ... P.start, trivially⟩` and uniq via `Subtype.ext` and `P.startUnique.uniq`. For the cast, note that `P.nodes ⟨0/k, ...⟩.castSucc = P.nodes 0` by `congr 1; exact Fin.ext (by simp)`. In the negative case, `P.depth = 0` (derive contradiction if depth > 0 using nonempty_of_depth_pos and Fintype.card_pos), so the type is `P.nodes (Fin.last 0)` which equals `P.nodes 0` by `congr; simp [Fin.last]`, and use `cast ... P.startUnique`.
-/
def obliviousNodes_zero_unique :
    Unique (ObliviousNodes P ⟨0, Nat.zero_lt_succ _⟩) := by
  simp only [ObliviousNodes]
  split_ifs with h
  · have heq : P.nodes (⟨0 / Fintype.card α, by
        exact Nat.div_lt_of_lt_mul (by linarith)⟩ : Fin P.depth).castSucc = P.nodes 0 := by
      congr 1; exact Fin.ext (by simp)
    exact {
      toInhabited := ⟨⟨cast heq.symm P.start, by simp [Fin.le_iff_val_le_val]⟩⟩
      uniq := fun ⟨w, hw⟩ => by
        apply Subtype.ext
        -- cast heq w = default = P.start, so w = cast heq.symm P.start
        have h2 := P.startUnique.uniq (cast heq w)
        -- h2 : cast heq w = default
        -- default = P.start, so cast heq w = P.start
        -- Therefore w = cast heq.symm (cast heq w) = cast heq.symm P.start
        have : w = cast heq.symm P.start := by
          apply_fun cast heq using (by exact fun a b h => by simpa using h)
          simp [h2]; rfl
        exact this
    }
  · have hd0 : P.depth = 0 := by
      by_contra h'
      have := Nat.pos_of_ne_zero h'
      have : Nonempty α := P.nonempty_of_depth_pos this
      exact h (Nat.mul_pos ‹_› Fintype.card_pos)
    exact cast (by congr 1; simp [Fin.last, hd0]) P.startUnique

end toOblivious

open toOblivious in
/-- Convert a `SkipBranchingProgram` to an oblivious `SkipBranchingProgram`.
Each original layer is expanded into `|α|` sub-layers, one per variable.
The new depth is `P.depth * |α|`, and obliviousness holds by construction since
all nodes in sub-layer `t` read the variable indexed by `t % |α|`. -/
def toOblivious : SkipBranchingProgram α β γ where
  depth := P.depth * Fintype.card α
  nodes := ObliviousNodes P
  nodeVar := fun {t} _u => ObliviousNodeVar P t
  edges := fun {t} u b => obliviousEdge P t u b
  edges_layer_gt := fun {t} u b => obliviousEdge_fst_gt P t u b
  startUnique := obliviousNodes_zero_unique P
  retVals := fun u => by
    show γ
    have : ObliviousNodes P (Fin.last (P.depth * Fintype.card α)) =
           P.nodes (Fin.last P.depth) := by
      unfold ObliviousNodes; simp [Fin.last]
    exact P.retVals (cast this u)

open toOblivious in
/-- The oblivious branching program produced by `toOblivious` is indeed oblivious:
all nodes in the same sub-layer read the same variable. -/
theorem toOblivious_IsOblivious : P.toOblivious.IsOblivious := by
  intro i j k
  simp [toOblivious, ObliviousNodeVar]

end SkipBranchingProgram
