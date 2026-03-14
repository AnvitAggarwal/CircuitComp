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
    set m := next.1
    set v := next.2
    have hm_bound : (m : ℕ) * Fintype.card α < P.depth * Fintype.card α + 1 :=
      Nat.lt_succ_of_le (Nat.mul_le_mul_right _ (Nat.le_of_lt_succ m.isLt))
    by_cases hml : (m : ℕ) * Fintype.card α < P.depth * Fintype.card α
    · refine ⟨⟨m * Fintype.card α, hm_bound⟩, ?_⟩
      rw [obliviousNodes_unfold P _ hml hk_pos]
      exact ⟨cast (by congr 1; exact Fin.ext (Nat.mul_div_cancel (m : ℕ) hk_pos).symm) v,
             by simp [Fin.le_iff_val_le_val]⟩
    · have hm_eq : (m : ℕ) = P.depth := by nlinarith [m.isLt]
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
             convert Nat.succ_le_of_lt hgt using 1
             simp [Fin.le_iff_val_le_val, *]
             grind⟩

/-- The edge target is strictly above the source layer. -/
lemma obliviousEdge_fst_gt (t : Fin (P.depth * Fintype.card α))
    (u : ObliviousNodes P t.castSucc) (b : β) :
    t.castSucc < (obliviousEdge P t u b).1 := by
    -- By definition of `obliviousEdge`, the first component of the edge is either `m * k` or `t + 1`, both of which are greater than `t`.
  simp [obliviousEdge]
  split_ifs <;> norm_num [Fin.lt_iff_val_lt_val] at *
  have := P.edges_layer_gt (cast (obliviousNodes_unfold P t.castSucc t.2 (Nat.pos_of_mul_pos_left (Fin.pos t))) u |>.1) b
  simp only [Fin.coe_castSucc, Fin.castSucc_mk, Fin.lt_iff_val_lt_val] at this
  nlinarith [Nat.div_add_mod t (Fintype.card α), Nat.mod_lt t (Nat.pos_of_mul_pos_left (Fin.pos t))]

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

/-- The oblivious branching program produced by `toOblivious` is indeed oblivious:
all nodes in the same sub-layer read the same variable. -/
theorem toOblivious_IsOblivious : P.toOblivious.IsOblivious := by
  intro i j k
  open toOblivious in
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
  suffices hsuff : ∀ (n : ℕ) (t : Fin (P.depth * Fintype.card α)) (u : ObliviousNodes P t.castSucc),
    P.depth * Fintype.card α - (t : ℕ) = n →
    P.toOblivious.evalAt x u = P.evalAt x (cast (obliviousNodes_unfold P t.castSucc t.isLt hk) u).1 from
    hsuff _ t u rfl
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro t u h_eq
    rw [P.toOblivious.evalAt_castSucc x t]
    change P.toOblivious.evalAt x (obliviousEdge P t u (x (ObliviousNodeVar P t))).snd = _
    simp only [obliviousEdge]
    split_ifs with hvar
    · rw [dif_pos hvar]
      conv_rhs => rw [P.evalAt_castSucc]
      rw [ObliviousNodeVar_eq_nodeVar P t hk _ hvar]
      split_ifs with hml
      · rw [dif_pos hml]
        dsimp only
        convert ih _ _ ⟨(P.edges (cast (toOblivious.obliviousNodes_unfold P t.castSucc t.2 hk) u |>.1) (x (P.nodeVar (cast (toOblivious.obliviousNodes_unfold P t.castSucc t.2 hk) u |>.1)))).1 * Fintype.card α, hml ⟩ _ rfl using 1
        convert rfl using 1
        · simp only [Fin.coe_castSucc, Fin.castSucc_mk, eq_mpr_eq_cast, cast_cast, cast_eq]
          congr! 1
          · exact Fin.ext (by simp [Nat.mul_div_cancel _ hk])
          · grind
        · rw [← h_eq]
          apply Nat.sub_lt_sub_left t.2
          · have := P.edges_layer_gt (cast (toOblivious.obliviousNodes_unfold P t.castSucc t.2 hk) u |>.1) (x (P.nodeVar (cast (toOblivious.obliviousNodes_unfold P t.castSucc t.2 hk) u |>.1)))
            simp_all only [Fin.castSucc, Fin.coe_castAdd, Fin.castSucc_mk, Fin.castAdd_mk]
            rw [Fin.lt_iff_val_lt_val] at this
            nlinarith only [this, Nat.div_add_mod t (Fintype.card α), Nat.mod_lt t hk]
      · rw [dif_neg hml]
        dsimp only
        unfold SkipBranchingProgram.toOblivious
        rw [SkipBranchingProgram.evalAt]
        simp only [Fin.coe_castSucc, Fin.castSucc_mk, Fin.ext_iff, Fin.last, Lean.Elab.WF.paramLet,
          Nat.succ_eq_add_one, ↓reduceDIte, eq_mpr_eq_cast, cast_cast, id_eq] at *
        rw [SkipBranchingProgram.evalAt]
        split_ifs with h
        · simp_all only [Nat.succ_eq_add_one, Fin.last]
          grind
        · exact False.elim <| h (Fin.eq_last_of_not_lt fun h => hml (Nat.mul_lt_mul_of_pos_right h hk))
    · rw [dif_neg hvar]
      dsimp only
      have ht1 : (t : ℕ) + 1 < P.depth * Fintype.card α := by
        have hgt := lt_of_le_of_ne (cast (obliviousNodes_unfold P t.castSucc t.isLt hk) u).2 (Ne.symm hvar)
        have hvar_lt := ((Fintype.equivFin α) (P.nodeVar (cast (obliviousNodes_unfold P t.castSucc t.isLt hk) u).1)).isLt
        have h_mod_lt : (t : ℕ) % Fintype.card α < Fintype.card α - 1 := by
          simp [Fin.lt_iff_val_lt_val] at hgt; omega
        have h_div_lt : (t : ℕ) / Fintype.card α < P.depth :=
          Nat.div_lt_of_lt_mul (by linarith [t.isLt])
        have h_decomp := Nat.div_add_mod (t : ℕ) (Fintype.card α)
        calc (t : ℕ) + 1
          _ ≤ (t : ℕ) / Fintype.card α * Fintype.card α + (Fintype.card α - 1) := by
              linarith
          _ < ((t : ℕ) / Fintype.card α + 1) * Fintype.card α := by
              rw [Nat.add_one_mul]; omega
          _ ≤ P.depth * Fintype.card α := Nat.mul_le_mul_right _ h_div_lt
      have h_meas : P.depth * Fintype.card α - ((t : ℕ) + 1) < n := by omega
      have h_ih := ih _ h_meas ⟨(t : ℕ) + 1, ht1⟩
      convert h_ih _ rfl using 1
      -- Since $t$ and $t + 1$ are consecutive, their divisions by $Fintype.card α$ are the same.
      have h_div_eq : (t : ℕ) / Fintype.card α = (t + 1 : ℕ) / Fintype.card α := by
        apply le_antisymm
        · simp [Nat.succ_div]
        simp only [Nat.succ_div, add_le_iff_nonpos_right, nonpos_iff_eq_zero, ite_eq_right_iff,
          one_ne_zero, imp_false]
        intro h_div
        have h_mod : (t : ℕ) % Fintype.card α = Fintype.card α - 1 := by
          obtain ⟨k, hk⟩ := h_div
          simp_all only [Fin.coe_castSucc, Fin.castSucc_mk, forall_const]
          rw [show (t : ℕ) = Fintype.card α * k - 1 from eq_tsub_of_add_eq hk]
          rcases k with (_ | k)
          · simp_all
          simp_all only [Nat.mul_succ]
          cases h : Fintype.card α
          · simp_all only [mul_zero, zero_tsub]
            linarith [Fin.is_lt t]
          · simp_all [Nat.add_mod, Nat.mul_succ]
        have h_contra : (Fintype.equivFin α) (P.nodeVar (cast (obliviousNodes_unfold P t.castSucc t.isLt hk) u).1) = ⟨Fintype.card α - 1, Nat.sub_lt hk zero_lt_one⟩ := by
          have h_contra : (Fintype.equivFin α) (P.nodeVar (cast (obliviousNodes_unfold P t.castSucc t.isLt hk) u).1) ≥ ⟨(t : ℕ) % Fintype.card α, Nat.mod_lt _ hk⟩ := by
            exact (cast (obliviousNodes_unfold P t.castSucc t.isLt hk) u).2
          exact le_antisymm (Nat.le_sub_one_of_lt (Fin.is_lt _)) (h_contra.trans' (by simp [h_mod]))
        exact hvar (h_contra.trans (by simp [h_mod]))
      simp only [Fin.coe_castSucc, Fin.castSucc_mk, eq_mpr_eq_cast, cast_cast, cast_eq]
      congr
      grind

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

/-- When `P.depth = 0`, the oblivious program trivially computes the same function. -/
private lemma toOblivious_eval_depth_zero (hd : P.depth = 0) :
    P.toOblivious.eval = P.eval := by
  ext1
  rw [eval, eval, toOblivious]
  open toOblivious in
  simp only [evalAt, Fin.zero_eq_last_iff, hd, zero_mul, ↓reduceDIte,
    start, obliviousNodes_zero_unique, eq_mpr_eq_cast]
  grind

open toOblivious in
/-- The width of the oblivious branching program is at most the width of the original. -/
theorem toOblivious_width_le : P.toOblivious.width ≤ P.width := by
  sorry

/-- The oblivious branching program computes the same function as the original. -/
theorem toOblivious_eval : P.toOblivious.eval = P.eval := by
  by_cases h : P.depth = 0
  · convert toOblivious_eval_depth_zero P h
  · ext x
    have h_card_pos : 0 < Fintype.card α := by
      exact P.nonempty_of_depth_pos (Nat.pos_of_ne_zero h) |> fun ⟨a⟩ => Fintype.card_pos_iff.mpr ⟨a⟩
    have h_eval_at_zero : P.toOblivious.evalAt x (P.toOblivious.start) = P.evalAt x P.start := by
      convert toOblivious_evalAt_of_lt P x ⟨0, Nat.zero_lt_succ _⟩ (by positivity) h_card_pos _ using 1
      congr! 1
      · simp
      · exact Subsingleton.helim (congrArg P.nodes ‹_›) _ _
    exact h_eval_at_zero

end SkipBranchingProgram
