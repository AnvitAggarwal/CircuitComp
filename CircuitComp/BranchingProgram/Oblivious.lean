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

omit [Fintype α] in
theorem toLayered_width [P.Finite] : P.toLayered.width = P.width := by
  simp only [ActiveNodes, ← Nat.card_sum, toLayered,
    SkipBranchingProgram.width, LayeredBranchingProgram.width]

omit [Fintype α] in
theorem toLayered_IsOblivious (h : P.IsOblivious) : P.toLayered.IsOblivious := by
  intro i j k
  rcases j with (j | ⟨j, hj⟩) <;> rcases k with (k | ⟨k, hk⟩)
  · exact h i j k
  · simp only [toLayered]
    rw [dif_pos ⟨j⟩]
    exact h i j _
  · simp only [toLayered]
    rw [dif_pos ⟨k⟩]
    exact h i _ k
  · rfl

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

/-- Unfolding lemma for `ObliviousNodes` at the last position. -/
lemma obliviousNodes_last (t : Fin (P.depth * Fintype.card α + 1))
  (ht : ¬(t : ℕ) < P.depth * Fintype.card α) :
    ObliviousNodes P t = P.nodes (Fin.last P.depth) := by
  simp only [ObliviousNodes, dif_neg ht]

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

/-- The edge target is strictly above the source layer. -/
lemma obliviousEdge_fst_gt (t : Fin (P.depth * Fintype.card α))
    (u : ObliviousNodes P t.castSucc) (b : β) :
    t.castSucc < (obliviousEdge P t u b).1 := by
    -- By definition of `obliviousEdge`, the first component of the edge is either `m * k` or `t + 1`, both of which are greater than `t`.
  simp [obliviousEdge];
  split_ifs <;> norm_num [ Fin.lt_iff_val_lt_val ] at *;
  have := P.edges_layer_gt ( cast ( obliviousNodes_unfold P t.castSucc t.2 ( Nat.pos_of_mul_pos_left ( Fin.pos t ) ) ) u |>.1 ) b; simp_all [ Fin.lt_iff_val_lt_val ] ;
  nlinarith [ Nat.div_add_mod t ( Fintype.card α ), Nat.mod_lt t ( Nat.pos_of_mul_pos_left ( Fin.pos t ) ) ]

/-- The type `ObliviousNodes P 0` is a `Unique` type, inheriting from `P.startUnique`. -/
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
        have h2 := P.startUnique.uniq (cast heq w)
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

lemma ObliviousNodeVar_eq_nodeVar (t : Fin (P.depth * Fintype.card α))
    (hk : 0 < Fintype.card α)
    (w : P.nodes (⟨(t : ℕ) / Fintype.card α, Nat.div_lt_of_lt_mul (by linarith [t.isLt])⟩ : Fin P.depth).castSucc)
    (hvar : (Fintype.equivFin α) (P.nodeVar w) = ⟨(t : ℕ) % Fintype.card α, Nat.mod_lt _ hk⟩) :
    ObliviousNodeVar P t = P.nodeVar w := by
  exact (Fintype.equivFin α).symm_apply_eq.mpr hvar.symm

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

open toOblivious in
/-- Core correspondence lemma: evalAt on the oblivious program at position `t.castSucc`
    equals evalAt on the original program at the underlying node. -/
private lemma toOblivious_evalAt_castSucc (x : α → β)
    (hk : 0 < Fintype.card α)
    (t : Fin (P.depth * Fintype.card α))
    (u : ObliviousNodes P t.castSucc) :
    P.toOblivious.evalAt x u =
    P.evalAt x (cast (obliviousNodes_unfold P t.castSucc t.isLt hk) u).1 := by
  sorry

open toOblivious in
/-- The main correspondence lemma for arbitrary positions. -/
private lemma toOblivious_evalAt_of_lt (x : α → β)
    (t : Fin (P.depth * Fintype.card α + 1))
    (ht : (t : ℕ) < P.depth * Fintype.card α)
    (hk : 0 < Fintype.card α)
    (u : ObliviousNodes P t) :
    P.toOblivious.evalAt x u =
    P.evalAt x (cast (obliviousNodes_unfold P t ht hk) u).1 := by
  exact toOblivious_evalAt_castSucc P x hk ⟨t, ht⟩ u

open toOblivious in
/-- When `P.depth = 0`, the oblivious program trivially computes the same function. -/
private lemma toOblivious_eval_depth_zero (hd : P.depth = 0) :
    P.toOblivious.eval = P.eval := by
  ext x
  rw [eval, eval, toOblivious]
  simp only [Lean.Elab.WF.paramLet, evalAt, Nat.succ_eq_add_one, Fin.zero_eq_last_iff, hd, zero_mul,
    ↓reduceDIte]
  simp only [start, obliviousNodes_zero_unique, Fin.zero_eta, hd, zero_mul, lt_self_iff_false,
    Fin.castSucc_mk, Nat.zero_mod, Lean.Elab.WF.paramLet, eq_mpr_eq_cast, cast_eq, ↓reduceDIte,
    cast_cast]
  grind

open toOblivious in
/-- The width of the oblivious branching program is at most the width of the original. -/
theorem toOblivious_width_le : P.toOblivious.width ≤ P.width := by
  sorry

open toOblivious in
/-- The oblivious branching program computes the same function as the original. -/
theorem toOblivious_eval : P.toOblivious.eval = P.eval := by
  by_cases h : P.depth = 0
  · convert toOblivious_eval_depth_zero P h
  · ext x
    have h_card_pos : 0 < Fintype.card α := by
      exact P.nonempty_of_depth_pos (Nat.pos_of_ne_zero h) |> fun ⟨a⟩ => Fintype.card_pos_iff.mpr ⟨a⟩
    have h_eval_at_zero : P.toOblivious.evalAt x (P.toOblivious.start) = P.evalAt x P.start := by
      convert toOblivious_evalAt_of_lt P x ⟨0, Nat.zero_lt_succ _⟩ (by positivity) h_card_pos _ using 1
      congr! 1;
      · simp
      · exact Subsingleton.helim (congrArg P.nodes ‹_›) _ _
    exact h_eval_at_zero

end SkipBranchingProgram
