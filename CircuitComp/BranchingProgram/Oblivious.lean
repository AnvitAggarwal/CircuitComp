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

namespace toOblivious

/-- Node type at depth `t` in `SkipBranchingProgram.toOblivious`. -/
def ObliviousNodes (t : Fin (P.depth * Fintype.card α + 1)) : Type v :=
  let k := Fintype.card α
  let E := Fintype.equivFin α
  if h : t < P.depth * k then
    let i : Fin P.depth := ⟨t / k, Nat.div_lt_of_lt_mul <| by linarith⟩
    let j : Fin k := ⟨t % k, Nat.mod_lt _ <| by clear i; contrapose! h; simp_all⟩
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
            simp +zetaDelta only [Fin.castSucc_mk] at hu' hgt ⊢
            simp only [Fin.lt_def]
            congr! 4
            · exact Fin.ext h_div
            · simp
           ⟩

/-- The edge target is strictly above the source layer. -/
lemma obliviousEdge_fst_gt (t : Fin (P.depth * Fintype.card α))
    (u : ObliviousNodes P t.castSucc) (b : β) :
    t.castSucc < (obliviousEdge P t u b).1 := by
    -- By definition of `obliviousEdge`, the first component of the edge is either `m * k` or `t + 1`, both of which are greater than `t`.
  simp [obliviousEdge]
  split_ifs <;> norm_num [Fin.lt_def] at *
  have := P.edges_layer_gt (cast (obliviousNodes_unfold P t.castSucc t.2 (Nat.pos_of_mul_pos_left (Fin.pos t))) u |>.1) b
  simp only [Fin.val_castSucc, Fin.castSucc_mk, Fin.lt_def] at this
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
        convert ih _ _ ⟨(P.edges (cast (toOblivious.obliviousNodes_unfold P t.castSucc t.2 hk) u |>.1) (x (P.nodeVar (cast (toOblivious.obliviousNodes_unfold P t.castSucc t.2 hk) u |>.1)))).1 * Fintype.card α, hml⟩ _ rfl using 1
        convert rfl using 1
        · simp only [Fin.val_castSucc, Fin.castSucc_mk, eq_mpr_eq_cast, cast_cast, cast_eq]
          congr! 1
          · exact Fin.ext (by simp [Nat.mul_div_cancel _ hk])
          · grind
        · rw [← h_eq]
          apply Nat.sub_lt_sub_left t.2
          · have := P.edges_layer_gt (cast (toOblivious.obliviousNodes_unfold P t.castSucc t.2 hk) u |>.1) (x (P.nodeVar (cast (toOblivious.obliviousNodes_unfold P t.castSucc t.2 hk) u |>.1)))
            simp_all only [Fin.castSucc, Fin.val_castAdd, Fin.castSucc_mk, Fin.castAdd_mk]
            rw [Fin.lt_def] at this
            nlinarith only [this, Nat.div_add_mod t (Fintype.card α), Nat.mod_lt t hk]
      · rw [dif_neg hml]
        dsimp only
        unfold SkipBranchingProgram.toOblivious
        rw [SkipBranchingProgram.evalAt]
        simp only [Fin.val_castSucc, Fin.castSucc_mk, Fin.ext_iff, Fin.last, Lean.Elab.WF.paramLet,
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
          simp [Fin.lt_def] at hgt; omega
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
          simp_all only [Fin.val_castSucc, Fin.castSucc_mk, forall_const]
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
      simp only [Fin.val_castSucc, Fin.castSucc_mk, eq_mpr_eq_cast, cast_cast, cast_eq]
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

omit [Fintype α] in
lemma width_layer_le (i : Fin (P.depth + 1)) :
    Nat.card (P.nodes i) + Nat.card (P.ActiveNodes i) ≤ P.width := by
  apply le_ciSup ?_ i
  exact Set.Finite.bddAbove (Set.finite_range _)

open toOblivious in
lemma toOblivious_nodes_card_le [P.Finite]
    (t : Fin (P.depth * Fintype.card α + 1))
    (ht : (t : ℕ) < P.depth * Fintype.card α)
    (hk : 0 < Fintype.card α) :
    Nat.card (ObliviousNodes P t) ≤
    Nat.card (P.nodes (⟨(t : ℕ) / Fintype.card α,
      Nat.div_lt_of_lt_mul (by linarith)⟩ : Fin P.depth).castSucc) := by
  rw [obliviousNodes_unfold P t ht hk]
  exact Finite.card_subtype_le _

section width_helpers
open toOblivious

private lemma obliviousEdge_passthrough_not_active
    (l₂ : Fin (P.depth * Fintype.card α))
    (v : ObliviousNodes P l₂.castSucc) (b : β)
    (hvar : ¬(Fintype.equivFin α) (P.nodeVar (cast (obliviousNodes_unfold P l₂.castSucc l₂.isLt
      (Nat.pos_of_mul_pos_left (Fin.pos l₂))) v).1) =
      ⟨(l₂ : ℕ) % Fintype.card α, Nat.mod_lt _ (Nat.pos_of_mul_pos_left (Fin.pos l₂))⟩) :
    (obliviousEdge P l₂ v b).1 = ⟨(l₂ : ℕ) + 1, by omega⟩ := by
  unfold obliviousEdge
  simp [hvar]

/-- Passthrough edges in obliviousEdge cannot produce active nodes: if the variable
doesn't match, the target layer is l₂+1, which is ≤ t when l₂ < t. -/
private lemma oblivious_active_passthrough_le
    (l₂ : Fin (P.depth * Fintype.card α))
    (v : ObliviousNodes P l₂.castSucc) (b : β)
    (hvar : ¬(Fintype.equivFin α) (P.nodeVar (cast (obliviousNodes_unfold P l₂.castSucc l₂.isLt
      (Nat.pos_of_mul_pos_left (Fin.pos l₂))) v).1) =
      ⟨(l₂ : ℕ) % Fintype.card α, Nat.mod_lt _ (Nat.pos_of_mul_pos_left (Fin.pos l₂))⟩)
    (t : Fin (P.depth * Fintype.card α + 1))
    (hl₂_lt : l₂.castSucc < t) :
    ¬((obliviousEdge P l₂ v b).1 > t) := by
  have := obliviousEdge_passthrough_not_active P l₂ v b hvar
  simpa [Fin.lt_def, this] using hl₂_lt

/-- When obliviousEdge does a variable-match jump, the target layer is m' * k
for some m' which is an original layer target. -/
private lemma oblivious_active_jump_layer
    (l₂ : Fin (P.depth * Fintype.card α))
    (v : ObliviousNodes P l₂.castSucc) (b : β)
    (hvar : (Fintype.equivFin α) (P.nodeVar (cast (obliviousNodes_unfold P l₂.castSucc l₂.isLt
      (Nat.pos_of_mul_pos_left (Fin.pos l₂))) v).1) =
      ⟨(l₂ : ℕ) % Fintype.card α, Nat.mod_lt _ (Nat.pos_of_mul_pos_left (Fin.pos l₂))⟩) :
    (obliviousEdge P l₂ v b).1.val =
      (P.edges (cast (obliviousNodes_unfold P l₂.castSucc l₂.isLt
        (Nat.pos_of_mul_pos_left (Fin.pos l₂))) v).1 b).1.val * Fintype.card α
    ∨ (obliviousEdge P l₂ v b).1.val = P.depth * Fintype.card α := by
  simp only [obliviousEdge, ↓reduceDIte, hvar]
  split <;> simp

/-- Every active node of the oblivious program at layer t comes from a variable-match jump,
NOT a passthrough. In particular, the obliviousEdge that created it satisfies the hvar
condition. This means the target layer m satisfies m = m'*k or m = depth*k
(by oblivious_active_jump_layer). -/
private lemma toOblivious_active_is_jump
    (t : Fin (P.depth * Fintype.card α + 1))
    (hk : 0 < Fintype.card α)
    (a : P.toOblivious.ActiveNodes t) :
    ∃ (l₂ : Fin (P.depth * Fintype.card α))
      (v : ObliviousNodes P l₂.castSucc) (b : β),
      l₂.castSucc < t ∧
      (Fintype.equivFin α) (P.nodeVar (cast (obliviousNodes_unfold P l₂.castSucc l₂.isLt hk) v).1) =
        ⟨(l₂ : ℕ) % Fintype.card α, Nat.mod_lt _ hk⟩ ∧
      obliviousEdge P l₂ v b = a.1 := by
  obtain ⟨l₂, hl₂_lt, v, b, hedge⟩ : ∃ l₂ : Fin (P.depth * Fintype.card α), l₂.castSucc < t ∧ ∃ v : ObliviousNodes P l₂.castSucc, ∃ b : β, obliviousEdge P l₂ v b = a.1 := by
    rcases a with ⟨⟨m, v⟩, hm₁, hm₂⟩
    exact hm₂
  by_cases hvar : (Fintype.equivFin α) (P.nodeVar (cast (obliviousNodes_unfold P l₂.castSucc l₂.isLt hk) v).1) = ⟨(l₂ : ℕ) % Fintype.card α, Nat.mod_lt _ hk⟩
  · exact ⟨l₂, v, b, hl₂_lt, hvar, hedge⟩
  · exact False.elim (absurd (oblivious_active_passthrough_le P l₂ v b hvar t hl₂_lt) (by simpa [hedge] using a.2.1))

/--The target layer of an oblivious active node at t is always a multiple of k. -/
private lemma toOblivious_active_target_div_k_mul
    (t : Fin (P.depth * Fintype.card α + 1))
    (hk : 0 < Fintype.card α)
    (a : P.toOblivious.ActiveNodes t) :
    Fintype.card α ∣ a.1.1.val := by
  obtain ⟨l₂, v, b, hl₂, hv, hb⟩ := toOblivious_active_is_jump P t hk a
  have h := oblivious_active_jump_layer P l₂ v b hv
  simp only [Fin.val_castSucc, Fin.castSucc_mk, hb] at h
  rcases h with h | h
  · simp only [dvd_mul_left, h]
  · simp only [dvd_mul_left, h]

/-- The underlying P layer of an oblivious active node target is > t/k. -/
private lemma toOblivious_active_target_layer_gt
    (t : Fin (P.depth * Fintype.card α + 1))
    (hk : 0 < Fintype.card α)
    (a : P.toOblivious.ActiveNodes t) :
    a.1.1.val / Fintype.card α > (t : ℕ) / Fintype.card α := by
  have h_gt_t : (a.1.1 : ℕ) > t := a.2.1
  have h_div := toOblivious_active_target_div_k_mul P t hk a
  apply Nat.div_lt_of_lt_mul
  linarith [Nat.div_mul_cancel h_div, Nat.div_mul_le_self t (Fintype.card α)]

/-- Extract the underlying P-sigma from an ObliviousNodes element at a layer divisible by k.
    At m < depth*k: the ObliviousNodes is a subtype of P.nodes, extract .val.
    At m ≥ depth*k: the ObliviousNodes IS P.nodes (Fin.last depth). -/
private noncomputable def obliviousNodeToPSigma
    (m : Fin (P.depth * Fintype.card α + 1))
    (hk : 0 < Fintype.card α)
    (w : ObliviousNodes P m) :
    (m' : Fin (P.depth + 1)) × P.nodes m' := by
  by_cases hlt : (m : ℕ) < P.depth * Fintype.card α
  · exact ⟨Fin.castSucc ⟨m.val / Fintype.card α, Nat.div_lt_of_lt_mul (by linarith)⟩,
           (cast (obliviousNodes_unfold P m hlt hk) w).val⟩
  · exact ⟨Fin.last P.depth, cast (obliviousNodes_last P m hlt) w⟩

/-- The P-sigma extraction map is injective: if two oblivious nodes at
divisible-by-k layers map to the same P-sigma, the original sigma pairs are equal. -/
private lemma obliviousNodeToPSigma_injective (hk : 0 < Fintype.card α)
    {m₁ m₂ : Fin (P.depth * Fintype.card α + 1)}
    (hm₁ : Fintype.card α ∣ m₁.val) (hm₂ : Fintype.card α ∣ m₂.val)
    {w₁ : ObliviousNodes P m₁} {w₂ : ObliviousNodes P m₂}
    (h : obliviousNodeToPSigma P m₁ hk w₁ = obliviousNodeToPSigma P m₂ hk w₂) :
    (Sigma.mk (β := ObliviousNodes P) m₁ w₁) = ⟨m₂, w₂⟩ := by
  have h_eq : m₁ = m₂ := by
    unfold obliviousNodeToPSigma at h
    split_ifs at h
    · simp_all [Fin.ext_iff]
    · simp [Fin.ext_iff] at h ⊢
      exact absurd h.1 (Nat.ne_of_lt (Nat.div_lt_of_lt_mul <| by linarith))
    · simp [Fin.ext_iff] at h ⊢
      exact absurd h.1 (by nlinarith [Nat.div_mul_cancel hm₂, Fin.is_lt m₂])
    · simp [Fin.ext_iff] at h ⊢
      linarith [Fin.is_lt m₁, Fin.is_lt m₂]
  subst h_eq
  grind [obliviousNodeToPSigma]

/-- The first component of obliviousNodeToPSigma is m / k. -/
private lemma obliviousNodeToPSigma_fst
    (m : Fin (P.depth * Fintype.card α + 1))
    (hk : 0 < Fintype.card α)
    (w : ObliviousNodes P m) :
    (obliviousNodeToPSigma P m hk w).fst.val = m.val / Fintype.card α := by
  unfold obliviousNodeToPSigma
  split_ifs
  · simp [Fin.castSucc]
  · simp only [Fin.last]
    rw [Nat.div_eq_of_eq_mul_left hk]
    omega

/--
The P-sigma of an oblivious active node's target equals some P.edges output,
    and the source layer of that edge is ≤ t/k. -/
private lemma active_pSigma_is_edge
    (t : Fin (P.depth * Fintype.card α + 1))
    (hk : 0 < Fintype.card α)
    (a : P.toOblivious.ActiveNodes t) :
    ∃ (i' : Fin P.depth) (v' : P.nodes i'.castSucc) (b' : β),
      i'.val ≤ (t : ℕ) / Fintype.card α ∧
      P.edges v' b' = obliviousNodeToPSigma P a.1.1 hk a.1.2 := by
  obtain ⟨l₂, v, b, hl₂_lt, hvar, hedge⟩ := toOblivious_active_is_jump P t hk a
  by_cases hml : (P.edges (cast (obliviousNodes_unfold P l₂.castSucc l₂.isLt hk) v).1 b).1.val * Fintype.card α < P.depth * Fintype.card α <;> simp_all [obliviousEdge]
  · refine ⟨⟨l₂.val / Fintype.card α, Nat.div_lt_of_lt_mul (by linarith [l₂.isLt])⟩, ?_, ?_⟩
    · exact Nat.div_le_div_right (Nat.le_of_lt hl₂_lt) |> le_trans <| by simp
    · unfold obliviousNodeToPSigma
      use (cast (obliviousNodes_unfold P l₂.castSucc l₂.isLt hk) v).1, b
      simp only [Fin.val_castSucc, Fin.castSucc_mk]
      cases a
      subst hedge
      simp_all only [↓reduceDIte, cast_cast, cast_eq]
      ext1
      · ext1
        simp_all only [Nat.mul_div_left]
      · simp_all only [heq_cast_iff_heq, heq_eq_eq]
  · refine ⟨⟨l₂.val / Fintype.card α, Nat.div_lt_of_lt_mul (by linarith [Fin.is_lt l₂])⟩, ?_, ?_⟩
    · exact Nat.div_le_div_right hl₂_lt.le
    · unfold obliviousNodeToPSigma
      simp only [← hedge, lt_self_iff_false]
      grind

/-- Under hall, the source of a variable-match jump must be in an earlier block. -/
private lemma active_source_block_lt_of_hall
    (t : Fin (P.depth * Fintype.card α + 1))
    (ht : (t : ℕ) < P.depth * Fintype.card α)
    (hk : 0 < Fintype.card α)
    (hall : ∀ w : P.nodes (⟨(t : ℕ) / Fintype.card α,
      Nat.div_lt_of_lt_mul (by linarith)⟩ : Fin P.depth).castSucc,
      (Fintype.equivFin α (P.nodeVar w)).val ≥ (t : ℕ) % Fintype.card α)
    (l₂ : Fin (P.depth * Fintype.card α))
    (v : ObliviousNodes P l₂.castSucc)
    (hl₂_lt : l₂.castSucc < t)
    (hvar : (Fintype.equivFin α) (P.nodeVar (cast (obliviousNodes_unfold P l₂.castSucc l₂.isLt hk) v).1) =
      ⟨(l₂ : ℕ) % Fintype.card α, Nat.mod_lt _ hk⟩) :
    l₂.val / Fintype.card α < t.val / Fintype.card α := by
  by_contra h_neg
  push_neg at h_neg
  have h_le : l₂.val / Fintype.card α ≤ t.val / Fintype.card α :=
    Nat.div_le_div_right (Nat.le_of_lt (by exact hl₂_lt))
  have h_eq : l₂.val / Fintype.card α = t.val / Fintype.card α := le_antisymm h_le h_neg
  have h_mod_lt : l₂.val % Fintype.card α < t.val % Fintype.card α := by
    nlinarith [Nat.div_add_mod l₂.val (Fintype.card α), Nat.div_add_mod t.val (Fintype.card α),
              show (l₂ : ℕ) < (t : ℕ) from hl₂_lt]
  have h_source : (↑((Fintype.equivFin α) (P.nodeVar (cast (obliviousNodes_unfold P l₂.castSucc l₂.isLt hk) v).1)) : ℕ) ≥
      t.val % Fintype.card α := by
    have h_layer_eq : P.nodes (Fin.castSucc ⟨l₂.val / Fintype.card α, Nat.div_lt_of_lt_mul (by linarith [l₂.isLt])⟩) =
        P.nodes (Fin.castSucc ⟨t.val / Fintype.card α, Nat.div_lt_of_lt_mul (by linarith)⟩) := by
      congr 1; ext; simp [Fin.castSucc]; exact h_eq
    have hsrc := hall (cast h_layer_eq (cast (obliviousNodes_unfold P l₂.castSucc l₂.isLt hk) v).val)
    convert hsrc using 3
    grind
  simp [hvar] at h_source
  omega

/-- Under hall, the source layer of the edge is strictly less than t/k. -/
private lemma active_pSigma_source_lt_of_hall
    (t : Fin (P.depth * Fintype.card α + 1))
    (ht : (t : ℕ) < P.depth * Fintype.card α)
    (hk : 0 < Fintype.card α)
    (hall : ∀ w : P.nodes (⟨(t : ℕ) / Fintype.card α,
      Nat.div_lt_of_lt_mul (by linarith)⟩ : Fin P.depth).castSucc,
      (Fintype.equivFin α (P.nodeVar w)).val ≥ (t : ℕ) % Fintype.card α)
    (a : P.toOblivious.ActiveNodes t) :
    ∃ (i' : Fin P.depth) (v' : P.nodes i'.castSucc) (b' : β),
      i'.val < (t : ℕ) / Fintype.card α ∧
      P.edges v' b' = obliviousNodeToPSigma P a.1.1 hk a.1.2 := by
  obtain ⟨l₂, v, b, hl₂_lt, hvar, hedge⟩ := toOblivious_active_is_jump P t hk a
  have h_lt := active_source_block_lt_of_hall P t ht hk hall l₂ v hl₂_lt hvar
  refine ⟨⟨l₂.val / Fintype.card α, Nat.div_lt_of_lt_mul (by linarith [l₂.isLt])⟩,
    (cast (obliviousNodes_unfold P l₂.castSucc l₂.isLt hk) v).val, b, h_lt, ?_⟩
  by_cases hml : (P.edges (cast (obliviousNodes_unfold P l₂.castSucc l₂.isLt hk) v).1 b).1.val * Fintype.card α < P.depth * Fintype.card α
  · simp_all only [obliviousEdge, ↓reduceDIte]
    unfold obliviousNodeToPSigma
    cases a
    subst hedge
    simp_all only [Fin.castSucc_mk, ↓reduceDIte]
    ext1
    · ext1
      simp only [Nat.mul_div_left, *]
    · simp only [heq_cast_iff_heq, heq_eq_eq, cast_cast, cast_eq, eq_mpr_eq_cast]
  · simp_all only [obliviousEdge, eq_mpr_eq_cast, mul_lt_mul_iff_left₀]
    unfold obliviousNodeToPSigma
    simp only [← hedge]
    grind

/-- Active nodes of P.toOblivious at any position t inject into
P.nodes at the next original layer ⊕ P.ActiveNodes at the next original layer. -/
private lemma toOblivious_active_card_le [Fintype β] [P.Finite]
    (t : Fin (P.depth * Fintype.card α + 1))
    (ht : (t : ℕ) < P.depth * Fintype.card α)
    (hk : 0 < Fintype.card α) :
    Nat.card (P.toOblivious.ActiveNodes t) ≤
    Nat.card (P.nodes (⟨(t : ℕ) / Fintype.card α,
      Nat.div_lt_of_lt_mul (by linarith)⟩ : Fin P.depth).succ) +
    Nat.card (P.ActiveNodes (⟨(t : ℕ) / Fintype.card α,
      Nat.div_lt_of_lt_mul (by linarith)⟩ : Fin P.depth).succ) := by
  obtain ⟨f, hf⟩ : ∃ f : P.toOblivious.ActiveNodes t → P.nodes (Fin.succ ⟨t / Fintype.card α, Nat.div_lt_of_lt_mul (by linarith)⟩) ⊕ P.ActiveNodes (Fin.succ ⟨t / Fintype.card α, Nat.div_lt_of_lt_mul (by linarith)⟩), Function.Injective f := by
    set i' : Fin P.depth := ⟨t.val / Fintype.card α, Nat.div_lt_of_lt_mul (by linarith)⟩
    set i : Fin (P.depth + 1) := Fin.castSucc i'
    refine' ⟨fun a => if h : (obliviousNodeToPSigma P a.1.1 hk a.1.2).fst.val = i'.val + 1 then Sum.inl (cast (by
    exact congr_arg _ (Fin.ext h)) (obliviousNodeToPSigma P a.1.1 hk a.1.2).snd) else Sum.inr ⟨(obliviousNodeToPSigma P a.1.1 hk a.1.2), by
      have h_gt : (obliviousNodeToPSigma P a.1.1 hk a.1.2).fst.val > i'.val + 1 := by
        have h_gt : (obliviousNodeToPSigma P a.1.1 hk a.1.2).fst.val > i'.val := by
          exact a.2.1 |> fun h => by simpa [obliviousNodeToPSigma_fst] using toOblivious_active_target_layer_gt P t hk a
        exact lt_of_le_of_ne h_gt (Ne.symm h) |> Nat.lt_of_le_of_lt (Nat.le_refl _) |> Nat.lt_of_lt_of_le <| Nat.le_refl _
      obtain ⟨l₂, v, b, hl₂, h_edge⟩ := active_pSigma_is_edge P t hk a
      exact ⟨h_gt, l₂, Nat.lt_succ_of_le hl₂, v, b, h_edge⟩⟩, _⟩
    intro a b hab
    have h_eq : obliviousNodeToPSigma P a.1.1 hk a.1.2 = obliviousNodeToPSigma P b.1.1 hk b.1.2 := by
      grind
    exact Subtype.ext <| obliviousNodeToPSigma_injective P hk (toOblivious_active_target_div_k_mul P t hk a) (toOblivious_active_target_div_k_mul P t hk b) h_eq
  have h_card_le : Nat.card (P.toOblivious.ActiveNodes t) ≤ Nat.card (P.nodes (Fin.succ ⟨t / Fintype.card α, Nat.div_lt_of_lt_mul (by linarith)⟩) ⊕ P.ActiveNodes (Fin.succ ⟨t / Fintype.card α, Nat.div_lt_of_lt_mul (by linarith)⟩)) := by
    have h_finite_active : Finite (P.ActiveNodes (Fin.succ ⟨t / Fintype.card α, Nat.div_lt_of_lt_mul (by linarith)⟩)) := by
      exact Set.Finite.to_subtype (Set.toFinite _)
    exact Nat.card_le_card_of_injective f hf
  -- Apply the fact that the cardinality of a sum type is the sum of the cardinalities of the individual types.
  have h_card_sum : Nat.card (P.nodes (Fin.succ ⟨t / Fintype.card α, Nat.div_lt_of_lt_mul (by linarith)⟩) ⊕ P.ActiveNodes (Fin.succ ⟨t / Fintype.card α, Nat.div_lt_of_lt_mul (by linarith)⟩)) = Nat.card (P.nodes (Fin.succ ⟨t / Fintype.card α, Nat.div_lt_of_lt_mul (by linarith)⟩)) + Nat.card (P.ActiveNodes (Fin.succ ⟨t / Fintype.card α, Nat.div_lt_of_lt_mul (by linarith)⟩)) := by
    exact @Nat.card_sum _ _ _ (Set.Finite.to_subtype (Set.toFinite _))
  exact h_card_sum ▸ h_card_le

private lemma toOblivious_active_le_of_all_ge [P.Finite]
    (t : Fin (P.depth * Fintype.card α + 1))
    (ht : (t : ℕ) < P.depth * Fintype.card α)
    (hk : 0 < Fintype.card α)
    (hall : ∀ w : P.nodes (⟨(t : ℕ) / Fintype.card α,
      Nat.div_lt_of_lt_mul (by linarith)⟩ : Fin P.depth).castSucc,
      (Fintype.equivFin α (P.nodeVar w)).val ≥ (t : ℕ) % Fintype.card α) :
    Nat.card (P.toOblivious.ActiveNodes t) ≤
    Nat.card (P.ActiveNodes (⟨(t : ℕ) / Fintype.card α,
      Nat.div_lt_of_lt_mul (by linarith)⟩ : Fin P.depth).castSucc) := by
  set i : Fin P.depth := ⟨(t : ℕ) / Fintype.card α, Nat.div_lt_of_lt_mul (by linarith)⟩ with i_def
  haveI : Finite (P.ActiveNodes i.castSucc) := by
    apply Finite.of_injective (f := fun (x : P.ActiveNodes i.castSucc) => x.1)
    intro a b h; exact Subtype.ext h
  apply Nat.card_le_card_of_injective
    (f := fun a => ⟨obliviousNodeToPSigma P a.1.1 hk a.1.2,
      by
        refine ⟨?_, ?_⟩
        · -- s.1 > i.castSucc
          have h1 := toOblivious_active_target_layer_gt P t hk a
          have h2 := obliviousNodeToPSigma_fst P a.1.1 hk a.1.2
          show (obliviousNodeToPSigma P a.1.1 _ a.1.2).1 > i.castSucc
          simp only [Fin.lt_def, Fin.val_castSucc]
          rw [h2]; exact h1
        · -- source witness
          obtain ⟨i', v', b', h_lt, h_edge⟩ := active_pSigma_source_lt_of_hall P t ht hk hall a
          refine ⟨i', ?_, v', b', h_edge⟩
          show i'.castSucc < i.castSucc
          simp only [Fin.lt_def, Fin.val_castSucc]
          exact h_lt
     ⟩)
  intro a₁ a₂ h_eq
  apply Subtype.ext
  refine obliviousNodeToPSigma_injective P hk ?_ ?_ (congrArg Subtype.val h_eq)
  · exact toOblivious_active_target_div_k_mul P t hk a₁
  · exact toOblivious_active_target_div_k_mul P t hk a₂

/-- When all nodes at layer i have equivFin(nodeVar) ≥ j (where j = t%k),
then total ≤ P.width. -/
private lemma toOblivious_total_le_of_all_ge [P.Finite]
    (t : Fin (P.depth * Fintype.card α + 1))
    (ht : (t : ℕ) < P.depth * Fintype.card α)
    (hk : 0 < Fintype.card α)
    (hall : ∀ w : P.nodes (⟨(t : ℕ) / Fintype.card α,
      Nat.div_lt_of_lt_mul (by linarith)⟩ : Fin P.depth).castSucc,
      (Fintype.equivFin α (P.nodeVar w)).val ≥ (t : ℕ) % Fintype.card α) :
    Nat.card (P.toOblivious.nodes t) + Nat.card (P.toOblivious.ActiveNodes t) ≤ P.width := by
  -- The cardinality of the nodes in the oblivious nodes at position t is equal to the cardinality of the nodes in the original program at layer i.castSucc.
  have h_nodes_card : Nat.card (P.toOblivious.nodes t) = Nat.card (P.nodes (⟨(t : ℕ) / Fintype.card α, Nat.div_lt_of_lt_mul (by linarith)⟩ : Fin P.depth).castSucc) := by
    have h_nodes_card : P.toOblivious.nodes t = { w : P.nodes (⟨(t : ℕ) / Fintype.card α, Nat.div_lt_of_lt_mul (by linarith)⟩ : Fin P.depth).castSucc // (Fintype.equivFin α (P.nodeVar w)).val ≥ (t : ℕ) % Fintype.card α } := by
      exact obliviousNodes_unfold P t ht hk ▸ rfl
    rw [h_nodes_card, Nat.card_congr (Equiv.subtypeUnivEquiv ?_)]
    exact hall
  refine le_trans (add_le_add h_nodes_card.le (toOblivious_active_le_of_all_ge P t ht hk hall)) ?_
  exact P.width_layer_le _

private lemma toOblivious_nodes_card_lt_of_exists_lt [P.Finite]
    (t : Fin (P.depth * Fintype.card α + 1))
    (ht : (t : ℕ) < P.depth * Fintype.card α)
    (hk : 0 < Fintype.card α)
    (hexists : ∃ w : P.nodes (⟨(t : ℕ) / Fintype.card α,
      Nat.div_lt_of_lt_mul (by linarith)⟩ : Fin P.depth).castSucc,
      (Fintype.equivFin α (P.nodeVar w)).val < (t : ℕ) % Fintype.card α) :
    Nat.card (ObliviousNodes P t) <
    Nat.card (P.nodes (⟨(t : ℕ) / Fintype.card α,
      Nat.div_lt_of_lt_mul (by linarith)⟩ : Fin P.depth).castSucc) := by
  rw [obliviousNodes_unfold P t ht hk]
  obtain ⟨w₀, hw₀⟩ := hexists
  exact Finite.card_subtype_lt hw₀.not_ge

end width_helpers

/-- The width of the oblivious branching program is at most double the width of the original:
Intuitively, one layer L gets split into several sub-layers. At sublayer k,
the `P.ActiveNodes` going past are present in `P.toOblivious` unchanged, and the nodes
in sublayer k contribute their width as before, as do the nodes in later sublayers (as ActiveNodes).
But the nodes in the earlier sublayers can split into up to `|β|` different `ActiveNodes`
depending on which value they read. So there's a `Fintype.card β * P.width` bound, but we can
improve this to a factor of 2.

Suppose the widest layer in `P` is layer L, and it has n nodes and a active nodes.

After toOblivious, it has a active nodes still, the last sublayer has `< n` nodes, and the
other (n-1) sublayer nodes contribute β each. They could point to up to β times as many.
Call that N. But the next layer has n' nodes and a' active nodes, and we know
that n' + a' ≤ n + a, because L was the widest. Now N + a is at most n' + a', since
each of those has to either end at the next layer, or go past there there and count as
an ActiveNode. So `N + a ≤ n' + a' ≤ n + a`, and the new width is less than
`n + a + N ≤ 2n + a ≤ 2(n + a) = 2 * P.width`. -/
theorem toOblivious_width_le [Fintype β] [P.Finite] : P.toOblivious.width < 2 * P.width := by
  open toOblivious in
  by_contra h_contra
  obtain ⟨t, ht⟩ : ∃ t : Fin (P.depth * Fintype.card α + 1), Nat.card (P.toOblivious.nodes t) + Nat.card (P.toOblivious.ActiveNodes t) ≥ 2 * P.width := by
    contrapose! h_contra
    convert lt_of_le_of_lt (ciSup_le fun t => Nat.le_sub_one_of_lt (h_contra t)) _ using 1
    exact Nat.sub_lt (mul_pos zero_lt_two (SkipBranchingProgram.width_pos P)) zero_lt_one
  by_cases ht_last : (t : ℕ) < P.depth * Fintype.card α
  · by_cases h_exists : ∃ w : P.nodes (⟨(t : ℕ) / Fintype.card α,
      Nat.div_lt_of_lt_mul (by linarith)⟩ : Fin P.depth).castSucc,
      (Fintype.equivFin α (P.nodeVar w)).val < (t : ℕ) % Fintype.card α
    · generalize_proofs pf at h_exists
      -- Apply the lemma that bounds the total number of nodes and active nodes at time `t` when there exists a node with a value less than `j`.
      have h_bound : Nat.card (P.toOblivious.nodes t) + Nat.card (P.toOblivious.ActiveNodes t) < 2 * P.width := by
        have := toOblivious_nodes_card_lt_of_exists_lt P t ht_last (Fintype.card_pos_iff.mpr ⟨P.nodeVar h_exists.choose⟩) h_exists
        have := toOblivious_active_card_le P t ht_last (Fintype.card_pos_iff.mpr ⟨P.nodeVar h_exists.choose⟩)
        have := width_layer_le P (Fin.castSucc ⟨(t : ℕ) / Fintype.card α, pf⟩)
        have := width_layer_le P (Fin.succ ⟨(t : ℕ) / Fintype.card α, pf⟩)
        linarith!
      grind
    · have h_total_le : Nat.card (P.toOblivious.nodes t) + Nat.card (P.toOblivious.ActiveNodes t) ≤ P.width := by
        apply toOblivious_total_le_of_all_ge P t ht_last
        · grind
        · exact fun w => not_lt.1 fun contra => h_exists ⟨w, contra⟩
      linarith [P.width_pos]
  · simp only [not_lt] at ht_last
    have ht_last_eq : t = Fin.last (P.depth * Fintype.card α) := by
      ext1
      linarith [Fin.is_lt t]
    simp only [ht_last_eq] at ht ⊢
    have h_card : Nat.card (P.toOblivious.nodes (Fin.last (P.depth * Fintype.card α))) = Nat.card (P.nodes (Fin.last P.depth)) := by
      exact Eq.symm (by unfold SkipBranchingProgram.toOblivious; simp [ObliviousNodes])
    simp only [h_card] at ht ⊢
    have h_card_active : Nat.card (P.toOblivious.ActiveNodes (Fin.last (P.depth * Fintype.card α))) = 0 := by
      rw [Nat.card_eq_zero]
      exact Or.inl <| by
        have := P.toOblivious.ActiveNodes_last_isEmpty
        exact ⟨fun u => this.false u⟩
    simp only [h_card_active, add_zero] at ht ⊢
    have h_card_le : Nat.card (P.nodes (Fin.last P.depth)) ≤ P.width := by
      exact le_trans (Nat.le_add_right _ _) (width_layer_le P (Fin.last P.depth)) |> le_trans (Nat.le_refl _) |> le_trans <| le_rfl
    linarith [P.width_pos]

/-- The oblivious branching program computes the same function as the original. -/
@[simp]
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
