import CircuitComp.BranchingProgram.Basic
import CircuitComp.ForMathlib

/-!
Proof that every Boolean function can be computed by branching program of width 3 and depth O(2^n).
This generalizes appropriately (with a larger width)to other types, with a finite number of
values for each input and a finite number of outputs.
-/

open LayeredBranchingProgram

noncomputable section

variable {α : Type u} {β : Type v} {γ : Type w}
variable [Fintype α] [Fintype β] [Fintype γ] [Nonempty α] [Nonempty β] (F : (α → β) → γ)

/-- Helper equivalences for defining `thinBP`. -/
noncomputable def thinBP_eab : Fin (Fintype.card β ^ Fintype.card α) ≃ (α → β) :=
  let ea := Fintype.equivFin α
  let eb := Fintype.equivFin β
  finFunctionFinEquiv.symm.trans (ea.symm.arrowCongr eb.symm)

abbrev thinBP_index : (α → β) ≃ Fin (Fintype.card β ^ Fintype.card α) :=
  thinBP_eab.symm

/--
Construct a think branching program for a function F. It keeps constant width but
has exponential depth.
-/
def thinBP : LayeredBranchingProgram α β γ :=
  letI c := Fintype.card γ
  haveI : NeZero c := ⟨(Fintype.card_pos_iff.mpr ⟨F (fun _ ↦ Classical.arbitrary β)⟩).ne'⟩
  letI ea := Fintype.equivFin α
  letI ec := Fintype.equivFin γ
  letI γ0 := ec.symm 0 --one particular value of γ
  { depth := Fintype.card α * Fintype.card β ^ Fintype.card α
    --Nodes are 2 special nodes, plus one more for each γ ... except for γ0.
    --We run through checks of each length-α string of β's, staying at (.inl 0) as long
    --as the check is passing, and failing to (.inl 1) if it fails. If we pass the
    --check, we branch to the corresponding γ node. Unless it's γ0, in which case we go
    --continue on (.inl 0). This special handling of γ0 only gets a reduction in width of 1,
    --but that's the difference between showing every Boolean function can be computed in width 3
    --and showing it can be computed in width 4, which is enough to care about!
    nodes i := if i = 0 then PUnit else ULift (Fin 2 ⊕ Fin (c - 1))
    nodeVar {i} _ := ea.symm ⟨i % Fintype.card α, Nat.mod_lt i Fintype.card_pos⟩
    edges {i} f j := by
      split_ifs with h₁
      · simp at h₁
      --The first layer is treated the same (.inl 0) on any other layer.
      if h_first : i.val = 0 ∨ (∃ h, f = cast (if_neg h).symm (ULift.up (.inl 0))) then
        -- This is (.inl 0). Continue a check, unless we're finishing a check in which case
        -- we branch to the appropriate output node.
        let nextβ := thinBP_eab (β := β)
          (⟨i.val / Fintype.card α, Nat.div_lt_of_lt_mul <| by omega⟩)
          (ea.symm ⟨i % Fintype.card α, Nat.mod_lt i Fintype.card_pos⟩)
        if nextβ = j then
          --The check passed. Continue on (.inl 0), unless we're at the end of the check.
          if i.val % Fintype.card α = Fintype.card α - 1 then
            --Get the output γ value from `F` and branch to the appropriate (.inr) node. But if it's γ0,
            -- we stay on (.inl 0) instead.
            let γOut := F (thinBP_eab (⟨i.val / Fintype.card α, Nat.div_lt_of_lt_mul <| by omega⟩))
            if hγOut : γOut = γ0 then
              exact .up (.inl 0)
            else
              exact .up (.inr ⟨ec γOut - 1,
                have : (ec γOut).val ≠ 0 := fun _ ↦ hγOut <| ec.injective (by aesop)
                by omega⟩)
          else
            --The check is continuing. Continue on (.inl 0).
            exact .up (.inl 0)
        else
          --The check failed. Continue on (.inl 1), unless that was the end of the check in which case
          -- we stay on (.inl 0) for the next check immediately.
          exact if i.val % Fintype.card α = Fintype.card α - 1 then
            --The check failed at the end. Reset back to (.inl 0) for the next check immediately.
            .up (.inl 0)
          else
            .up (.inl 1)
      else
      have hf₁ : ¬i.castSucc = 0 := (h_first <| .inl <| Fin.ext_iff.mp ·)
      revert f
      rw! [if_neg hf₁]
      intro f h_first
      rcases hf : f.down with (_ | _) | val
      · --This is impossible because of h_first
        exfalso
        exact (show f ≠ .up (.inl 0) from (h_first <| .inr ⟨hf₁, ·⟩)) (by ext; simpa)
      · -- This is (.inl 1). Do nothing and stay, unless we just finished a check and so
        -- we reset back to (.inl 0).
        exact if i.val % Fintype.card α = Fintype.card α - 1 then
          .up (.inl 0)
        else
          .up (.inl 1)
      · -- We're on a γ-valued node. Continue and keep this value.
        exact .up (.inr val)
    startUnique := {
      default := PUnit.unit,
      uniq := by simp
    }
    retVals f := by
      split_ifs at f with h
      · --Impossible
        exfalso
        simp +zetaDelta at h
      · rcases f.down with _ | val
        · exact γ0
        · exact ec.symm ⟨val + 1, by omega⟩
  }

instance thinBP_Finite [Fintype β] : (thinBP F).Finite where
  finite i := by
    dsimp [thinBP]
    split
    · infer_instance
    · infer_instance

theorem thinBP_IsOblivious : (thinBP F).IsOblivious :=
  fun _ _ _ ↦ rfl

theorem thinBP_width : (thinBP F).width = Fintype.card γ + 1 := by
  dsimp [thinBP, width]
  apply le_antisymm
  · refine ciSup_le (fun i ↦ ?_)
    split
    · simp
    · have : Fintype.card γ ≠ 0 := by
        exact (Fintype.card_pos_iff.mpr ⟨F (fun _ ↦ Classical.arbitrary β)⟩).ne'
      grind [Nat.card_eq_fintype_card, Fintype.card_ulift, Fintype.card_sum, Fintype.card_fin]
  · refine le_trans ?_ (le_ciSup ?_ ⟨Fintype.card α * Fintype.card β ^ Fintype.card α, ?_⟩)
    · simp only [lt_add_iff_pos_right, zero_lt_one, Fin.mk_eq_zero, mul_eq_zero,
      Fintype.card_ne_zero, Nat.pow_eq_zero]
      grind [Nat.card_eq_fintype_card, Fintype.card_ulift, Fintype.card_sum, Fintype.card_fin]
    · simp
    · simp

-------------
--Proving the correctness of `thinBP`.
section thinBP_proof

theorem thinBP_depth : (thinBP F).depth = Fintype.card α * Fintype.card β ^ Fintype.card α := by
  rfl

instance thinBP_depth_pos : NeZero (thinBP F).depth := by
  rw [thinBP_depth]
  constructor
  positivity

/-- Auxiliary predicate for `thinBP_CorrectState`: does the first `pos` symbols of `x` match
the target string defined by `k`? -/
def thinBP_match (k : Fin (Fintype.card β ^ Fintype.card α)) (pos : ℕ)
    (h_pos : pos ≤ Fintype.card α) (x : α → β) : Prop :=
  let target := thinBP_eab (α := α) (β := β) k
  let ea := Fintype.equivFin α
  ∀ j : Fin pos, x (ea.symm ⟨j, by omega⟩) = target (ea.symm ⟨j, by omega⟩)

omit [Nonempty α] [Nonempty β] in
lemma thinBP_match_zero (k : Fin (Fintype.card β ^ Fintype.card α)) (x : α → β) (h : 0 ≤ Fintype.card α):
    thinBP_match k 0 h x :=
  fun j ↦ by cases j; trivial

omit [Nonempty α] [Nonempty β] in
lemma thinBP_match_succ (k : Fin (Fintype.card β ^ Fintype.card α)) (pos : ℕ) (h_pos : pos + 1 ≤ Fintype.card α) (x : α → β) :
    thinBP_match k (pos + 1) h_pos x ↔
    thinBP_match k pos (by omega) x ∧
    x ((Fintype.equivFin α).symm ⟨pos, by omega⟩) =
      thinBP_eab k ((Fintype.equivFin α).symm ⟨pos, by omega⟩) := by
  unfold thinBP_match
  constructor
  · exact fun h ↦ ⟨fun j ↦ h ⟨j, by omega⟩, h ⟨pos, by omega⟩⟩
  · exact fun h j ↦ by cases j using Fin.lastCases <;> simp [*]

omit [Nonempty α] [Nonempty β] in
private lemma thinBP_match_congr {k1 k2 : Fin (Fintype.card β ^ Fintype.card α)} {pos1 pos2 : ℕ}
    {h1 : pos1 ≤ Fintype.card α} {h2 : pos2 ≤ Fintype.card α} {x : α → β}
    (hk : k1 = k2) (hp : pos1 = pos2) :
    thinBP_match k1 pos1 h1 x ↔ thinBP_match k2 pos2 h2 x := by
  subst hk; subst hp; rfl

omit [Nonempty α] [Nonempty β] in
lemma thinBP_match_card (k : Fin (Fintype.card β ^ Fintype.card α)) (x : α → β) :
    thinBP_match k (Fintype.card α) (by omega) x ↔ thinBP_index x = k := by
  constructor <;> intro h
  · have h_eq : x = thinBP_eab k := by
      ext a
      have := h (Fintype.equivFin α a)
      simp_all
    simp [h_eq]
  · simp [← h, thinBP_match]

open Classical in
/-- The state of the BP at a node `s` when running `x`. We'll inductively prove this claim. -/
def thinBP_CorrectState (i : Fin ((thinBP F).depth + 1)) (x : α → β) (s : (thinBP F).nodes i) : Prop :=
  if h : i.val = 0 then
    HEq s PUnit.unit
  else
    let a := Fintype.card α
    let b := Fintype.card β
    let c := Fintype.card γ
    haveI : NeZero c := ⟨(Fintype.card_pos_iff.mpr ⟨F (fun _ ↦ Classical.arbitrary β)⟩).ne'⟩
    let k := (i : ℕ) / a
    let pos := (i : ℕ) % a
    let idx := thinBP_index x
    let ec := Fintype.equivFin γ
    let γ0 := ec.symm 0
    let s' : ULift (Fin 2 ⊕ Fin (c - 1)) := cast (by
      dsimp [thinBP]
      rw [if_neg]
      intro h_eq
      apply h
      exact Fin.ext_iff.mp h_eq
    ) s
    if h_found : idx < k ∧ F x ≠ γ0 then
      s' = ULift.up (Sum.inr (Fin.mk ((ec (F x)).val - 1) (by
        have : F x ≠ ec.symm 0 := h_found.2
        have : ec (F x) ≠ 0 := by
          intro h_eq
          apply this
          rw [← h_eq, Equiv.symm_apply_apply]
        have h_val : (ec (F x)).val ≠ 0 := by
          intro h
          apply this
          ext
          exact h
        have h_lt : (ec (F x)).val < c := (ec (F x)).is_lt
        omega)))
    else if hk : k < b ^ a then
      if thinBP_match (Fin.mk k hk) pos (le_of_lt (Nat.mod_lt i Fintype.card_pos)) x then
        s' = ULift.up (Sum.inl 0)
      else
        s' = ULift.up (Sum.inl 1)
    else
      s' = ULift.up (Sum.inl 0)

theorem thinBP_CorrectState_zero {s} (x : α → β) :
    thinBP_CorrectState F 0 x s := by
  simp only [thinBP_CorrectState, heq_eq_eq]
  apply Subsingleton.elim

theorem thinBP_CorrectState_one (x : α → β) :
    thinBP_CorrectState F 1 x (evalLayer (thinBP F) 1 x) := by
  have ha : 0 < Fintype.card α := by
    positivity
  have h_cond2 : 0 < Fintype.card β ^ Fintype.card α := by
    positivity
  have h_depth : 1 < (thinBP F).depth + 1 := by
    rw [thinBP_depth]
    rw [← Nat.add_one_le_iff] at ha h_cond2
    grw [← h_cond2, ← ha]
    norm_num
  simp only [thinBP_CorrectState, Fin.coe_ofNat_eq_mod, Nat.one_mod_eq_zero_iff, Nat.add_eq_right,
    (thinBP_depth_pos F).out, ↓reduceDIte, ne_eq, Fin.isValue]
  let _ := @Classical.inhabited_of_nonempty α ‹_›
  rcases nontrivialPSumUnique α with h_2a | h_uniq
  · have hcα : 1 < Fintype.card α := by
      rwa [Fintype.one_lt_card_iff_nontrivial]
    have h_cond1 : 1 % ((thinBP F).depth + 1) / Fintype.card α = 0 := by
      apply Nat.div_eq_of_lt
      rwa [Nat.mod_eq_of_lt h_depth]
    have hz : ¬(0 = Fintype.card α - 1) := by
      omega
    simp only [h_cond1, not_lt_zero', false_and, ↓reduceDIte, h_cond2, Fin.mk_zero', Fin.isValue,
      Fin.coe_ofNat_eq_mod]
    rw! [h_cond1, Fin.mk_zero']
    rw! [show (1 : Fin (thinBP F).depth.succ) = Fin.succ 0 by simp]
    simp only [evalLayer_succ, Fin.castSucc_zero, cast_eq, Fin.isValue, evalLayer_zero]
    simp only [thinBP, Fin.castSucc_eq_zero_iff, Fin.succ_ne_zero, ↓reduceDIte, ↓dreduceIte,
      Fin.val_eq_zero_iff, Fin.isValue, dite_eq_ite, cast_eq, Fin.zero_eta, id_eq, eq_mpr_eq_cast,
      Fin.last_eq_zero_iff, mul_eq_zero, Fintype.card_ne_zero, Nat.pow_eq_zero, ne_eq,
      not_false_eq_true, and_true, or_self, eq_mp_eq_cast, ↓dreduceDIte, Lean.Elab.WF.paramLet,
      Fin.coe_ofNat_eq_mod, Nat.zero_mod, Fin.mk_zero', Fin.castSucc_zero, not_true_eq_false,
      IsEmpty.exists_iff, or_false, Nat.zero_div, hz, ↓reduceIte, ite_eq_left_iff, ULift.up.injEq,
      Sum.inl.injEq, one_ne_zero, imp_false, not_not, ite_eq_right_iff, zero_ne_one]
    have h_cond3 : 1 % (Fintype.card α * Fintype.card β ^ Fintype.card α + 1) % Fintype.card α = 1 := by
      have h4 : 1 % (Fintype.card α * Fintype.card β ^ Fintype.card α + 1) = 1 :=
        Nat.mod_eq_of_lt h_depth
      rwa [h4, Nat.mod_eq_of_lt]
    rw! [h_cond3, thinBP_match_succ]
    rw [eq_true (thinBP_match_zero _ _ _), true_and, eq_comm]
    split_ifs with h <;> exact h
  · have h_cond1 : 1 % ((thinBP F).depth + 1) / 1 = 1 := by
      simpa using h_depth
    simp only [Fintype.card_unique, Nat.div_one, pow_one, isUnit_iff_eq_one, IsUnit.dvd,
      Nat.mod_mod_of_dvd, Nat.mod_self, Fin.isValue, Fin.coe_ofNat_eq_mod]
    have ha : Fintype.card α = 1 := Fintype.card_unique
    rw! (castMode := .all) [ha, Nat.mod_one]
    rw! [h_cond1]
    conv =>
      enter [3, h, 2, h₂]
      rw [if_pos (thinBP_match_zero _ _ _)]
    rw! [show (1 : Fin (thinBP F).depth.succ) = Fin.succ 0 by simp]
    simp only [evalLayer_succ, Fin.castSucc_zero, cast_eq, Fin.isValue, evalLayer_zero]
    simp only [Nat.lt_one_iff, Fin.val_eq_zero_iff, thinBP, Fin.castSucc_eq_zero_iff,
      Fin.succ_ne_zero, ↓dreduceDIte, ↓dreduceIte, Fin.isValue, Fintype.card_unique, tsub_self,
      Lean.Elab.WF.paramLet, Nat.div_one, dite_eq_ite, cast_eq, Fin.zero_eta, id_eq, eq_mpr_eq_cast,
      Fin.last_eq_zero_iff, pow_one, one_mul, Fintype.card_ne_zero, eq_mp_eq_cast,
      Fin.coe_ofNat_eq_mod, Nat.zero_mod, Nat.mod_succ, Fin.mk_zero', Fin.castSucc_zero,
      not_true_eq_false, IsEmpty.exists_iff, or_false, ↓reduceDIte, ↓reduceIte, ite_eq_right_iff,
      dite_eq_left_iff, ULift.up.injEq, reduceCtorEq, imp_false, not_not, ite_self]
    split_ifs with h₁ h₂ h₃
    · exfalso
      apply h₁.right
      convert h₃
      ext1
      simpa [Unique.eq_default] using h₂.symm
    · congr 7
      simpa [ha, funext_iff, Unique.eq_default] using h₂
    · exfalso
      -- Since α has only one element, the function x is determined entirely by its value at that element. Therefore, the index of x should be the same as the index of the constant function.
      have h_const : x = fun _ => x (Classical.arbitrary α) := by
        exact funext fun a => by rw [ Fintype.card_eq_one_iff ] at ha; obtain ⟨ b, hb ⟩ := ha; aesop;
      rw [ h_const ] at h₁
      simp [thinBP_index] at h₁
      convert (thinBP_index.symm.apply_eq_iff_eq_symm_apply
        (x := ⟨0, h_cond2⟩) (y := fun _ ↦ x (Classical.arbitrary α))).mpr _;
      · grind
      · convert h₁.1.symm using 1;
        · rw [ ha ];
        · exact (Fin.heq_ext_iff (congrArg (HPow.hPow (Fintype.card β)) ha)).mpr rfl;
        · congr! 1;
          · rw [ ha ];
          · exact funext fun _ => by rw [ ha ] ;
          · grind;
          · grind;
    · push_neg at h₁
      simp only [Nat.lt_one_iff, Fin.val_eq_zero_iff] at h₁
      have hx_const : ∃ b : β, x = fun _ => b := by
        exact ⟨x default, funext fun a => by rw [ show a = default from Subsingleton.elim _ _ ]⟩
      obtain ⟨b, rfl⟩ := hx_const
      intro h
      simp only [thinBP_index] at h₁ h
      convert h₁ _ using 2
      · simpa [funext_iff, Unique.eq_default] using h
      · convert congr_arg ( (thinBP_eab (α := α) (β := β)).symm ) ( show ( fun _ => b ) = thinBP_eab 0 from _ ) using 1;
        any_goals exact congrArg Fin (congrArg (HPow.hPow (Fintype.card β)) (id (Eq.symm ha)));
        · congr! 2
          · expose_names
            exact
              Equiv.instEquivLike.hcongr_2 (α → β) (α → β) rfl (Fin (Fintype.card β ^ 1))
                (Fin (Fintype.card β ^ Fintype.card α)) e_1
          · grind;
        · simp
          grind only
        · ext1
          simp [Unique.eq_default, ← h]

/- Edge transition lemmas for thinBP -/

private lemma thinBP_nodes_eq' (i : Fin ((thinBP F).depth + 1)) (hi : i ≠ 0) :
    (thinBP F).nodes i = ULift (Fin 2 ⊕ Fin (Fintype.card γ - 1)) := by
  simp [thinBP, hi]

private lemma thinBP_k_bound' (i : Fin (thinBP F).depth) :
    (i : ℕ) / Fintype.card α < Fintype.card β ^ Fintype.card α := by
  apply Nat.div_lt_of_lt_mul
  simpa only [thinBP_depth] using i.isLt

private lemma thinBP_edge_inr' (i : Fin (thinBP F).depth) (hi : i.castSucc ≠ 0)
    (x : α → β) (val : Fin (Fintype.card γ - 1))
    (hs : cast (thinBP_nodes_eq' F i.castSucc hi) (evalLayer (thinBP F) i.castSucc x) =
      ULift.up (Sum.inr val)) :
    cast (thinBP_nodes_eq' F i.succ (Fin.succ_ne_zero i))
      (evalLayer (thinBP F) i.succ x) = ULift.up (Sum.inr val) := by
  have : (thinBP F).evalLayer i.succ x = (thinBP F).edges ((thinBP F).evalLayer i.castSucc x) _ :=
    rfl
  rcases i with ⟨_ | i, _⟩
  · simp at hi
  rw [cast_comm] at hs
  rw [this, cast_comm, hs]
  simp [thinBP]

private lemma thinBP_edge_inl1_boundary' (i : Fin (thinBP F).depth) (hi : i.castSucc ≠ 0)
    (x : α → β) (h_boundary : (i : ℕ) % Fintype.card α = Fintype.card α - 1)
    (hs : cast (thinBP_nodes_eq' F i.castSucc hi) (evalLayer (thinBP F) i.castSucc x) =
      ULift.up (Sum.inl 1)) :
    cast (thinBP_nodes_eq' F i.succ (Fin.succ_ne_zero i))
      (evalLayer (thinBP F) i.succ x) = ULift.up (Sum.inl 0) := by
  have : (thinBP F).evalLayer i.succ x = (thinBP F).edges ((thinBP F).evalLayer i.castSucc x) _ :=
    rfl
  rcases i with ⟨_ | i, _⟩
  · simp at hi
  rw [cast_comm] at hs
  rw [this, cast_comm, hs]
  simp [thinBP, h_boundary]

private lemma thinBP_edge_inl1_interior' (i : Fin (thinBP F).depth) (hi : i.castSucc ≠ 0)
    (x : α → β) (h_not_boundary : (i : ℕ) % Fintype.card α ≠ Fintype.card α - 1)
    (hs : cast (thinBP_nodes_eq' F i.castSucc hi) (evalLayer (thinBP F) i.castSucc x) =
      ULift.up (Sum.inl 1)) :
    cast (thinBP_nodes_eq' F i.succ (Fin.succ_ne_zero i))
      (evalLayer (thinBP F) i.succ x) = ULift.up (Sum.inl 1) := by
  have h_edge : (thinBP F).edges (evalLayer (thinBP F) i.castSucc x) (x ((Fintype.equivFin α).symm ⟨i.val % Fintype.card α, Nat.mod_lt _ Fintype.card_pos⟩)) = ULift.up (Sum.inl 1) := by
    generalize_proofs at *
    rcases i with ⟨_ | i, hi⟩
    · simp at hi
    · simp only [cast_eq, Fin.isValue] at hs
      simp only [hs]
      simp [thinBP, h_not_boundary]
  rw [← h_edge, evalLayer_succ]
  simp [thinBP]

private lemma thinBP_edge_inl0_match_interior' (i : Fin (thinBP F).depth) (hi : i.castSucc ≠ 0)
    (x : α → β) (h_not_boundary : (i : ℕ) % Fintype.card α ≠ Fintype.card α - 1)
    (h_match : x ((Fintype.equivFin α).symm ⟨(i : ℕ) % Fintype.card α,
        Nat.mod_lt i Fintype.card_pos⟩) =
      thinBP_eab (α := α) (β := β) ⟨(i : ℕ) / Fintype.card α, thinBP_k_bound' F i⟩
        ((Fintype.equivFin α).symm ⟨(i : ℕ) % Fintype.card α, Nat.mod_lt i Fintype.card_pos⟩))
    (hs : cast (thinBP_nodes_eq' F i.castSucc hi) (evalLayer (thinBP F) i.castSucc x) =
      ULift.up (Sum.inl 0)) :
    cast (thinBP_nodes_eq' F i.succ (Fin.succ_ne_zero i))
      (evalLayer (thinBP F) i.succ x) = ULift.up (Sum.inl 0) := by
  rw [cast_comm] at hs
  rw [evalLayer_succ, hs]
  simp [thinBP, thinBP_eab] at h_match ⊢
  grind

private lemma thinBP_edge_inl0_nomatch_interior' (i : Fin (thinBP F).depth) (hi : i.castSucc ≠ 0)
    (x : α → β) (h_not_boundary : (i : ℕ) % Fintype.card α ≠ Fintype.card α - 1)
    (h_nomatch : x ((Fintype.equivFin α).symm ⟨(i : ℕ) % Fintype.card α,
        Nat.mod_lt i Fintype.card_pos⟩) ≠
      thinBP_eab (α := α) (β := β) ⟨(i : ℕ) / Fintype.card α, thinBP_k_bound' F i⟩
        ((Fintype.equivFin α).symm ⟨(i : ℕ) % Fintype.card α, Nat.mod_lt i Fintype.card_pos⟩))
    (hs : cast (thinBP_nodes_eq' F i.castSucc hi) (evalLayer (thinBP F) i.castSucc x) =
      ULift.up (Sum.inl 0)) :
    cast (thinBP_nodes_eq' F i.succ (Fin.succ_ne_zero i))
      (evalLayer (thinBP F) i.succ x) = ULift.up (Sum.inl 1) := by
  dsimp [thinBP] at hs ⊢
  rw [LayeredBranchingProgram.evalLayer_succ]
  grind

private lemma thinBP_edge_inl0_nomatch_boundary' (i : Fin (thinBP F).depth) (hi : i.castSucc ≠ 0)
    (x : α → β) (h_boundary : (i : ℕ) % Fintype.card α = Fintype.card α - 1)
    (h_nomatch : x ((Fintype.equivFin α).symm ⟨(i : ℕ) % Fintype.card α,
        Nat.mod_lt i Fintype.card_pos⟩) ≠
      thinBP_eab (α := α) (β := β) ⟨(i : ℕ) / Fintype.card α, thinBP_k_bound' F i⟩
        ((Fintype.equivFin α).symm ⟨(i : ℕ) % Fintype.card α, Nat.mod_lt i Fintype.card_pos⟩))
    (hs : cast (thinBP_nodes_eq' F i.castSucc hi) (evalLayer (thinBP F) i.castSucc x) =
      ULift.up (Sum.inl 0)) :
    cast (thinBP_nodes_eq' F i.succ (Fin.succ_ne_zero i))
      (evalLayer (thinBP F) i.succ x) = ULift.up (Sum.inl 0) := by
  dsimp [thinBP] at hs ⊢
  rw [LayeredBranchingProgram.evalLayer_succ]
  grind

private lemma thinBP_edge_inl0_match_boundary_gamma0' [NeZero (Fintype.card γ)] (i : Fin (thinBP F).depth) (hi : i.castSucc ≠ 0)
    (x : α → β) (h_boundary : (i : ℕ) % Fintype.card α = Fintype.card α - 1)
    (h_match : x ((Fintype.equivFin α).symm ⟨(i : ℕ) % Fintype.card α,
        Nat.mod_lt i Fintype.card_pos⟩) =
      thinBP_eab (α := α) (β := β) ⟨(i : ℕ) / Fintype.card α, thinBP_k_bound' F i⟩
        ((Fintype.equivFin α).symm ⟨(i : ℕ) % Fintype.card α, Nat.mod_lt i Fintype.card_pos⟩))
    (h_gamma0 : F (thinBP_eab ⟨(i : ℕ) / Fintype.card α, thinBP_k_bound' F i⟩) =
      (Fintype.equivFin γ).symm 0)
    (hs : cast (thinBP_nodes_eq' F i.castSucc hi) (evalLayer (thinBP F) i.castSucc x) =
      ULift.up (Sum.inl 0)) :
    cast (thinBP_nodes_eq' F i.succ (Fin.succ_ne_zero i))
      (evalLayer (thinBP F) i.succ x) = ULift.up (Sum.inl 0) := by
  dsimp [thinBP] at hs ⊢
  rw [LayeredBranchingProgram.evalLayer_succ]
  grind

private lemma thinBP_edge_inl0_match_boundary_not_gamma0' [NeZero (Fintype.card γ)] (i : Fin (thinBP F).depth) (hi : i.castSucc ≠ 0)
    (x : α → β) (h_boundary : (i : ℕ) % Fintype.card α = Fintype.card α - 1)
    (h_match : x ((Fintype.equivFin α).symm ⟨(i : ℕ) % Fintype.card α,
        Nat.mod_lt i Fintype.card_pos⟩) =
      thinBP_eab (α := α) (β := β) ⟨(i : ℕ) / Fintype.card α, thinBP_k_bound' F i⟩
        ((Fintype.equivFin α).symm ⟨(i : ℕ) % Fintype.card α, Nat.mod_lt i Fintype.card_pos⟩))
    (h_not_gamma0 : F (thinBP_eab ⟨(i : ℕ) / Fintype.card α, thinBP_k_bound' F i⟩) ≠
      (Fintype.equivFin γ).symm 0)
    (hs : cast (thinBP_nodes_eq' F i.castSucc hi) (evalLayer (thinBP F) i.castSucc x) =
      ULift.up (Sum.inl 0)) :
    cast (thinBP_nodes_eq' F i.succ (Fin.succ_ne_zero i))
      (evalLayer (thinBP F) i.succ x) =
    ULift.up (Sum.inr ⟨((Fintype.equivFin γ)
        (F (thinBP_eab ⟨(i : ℕ) / Fintype.card α, thinBP_k_bound' F i⟩))).val - 1, by
        have h_ne : (Fintype.equivFin γ) (F (thinBP_eab ⟨(i : ℕ) / Fintype.card α,
          thinBP_k_bound' F i⟩)) ≠ 0 := by
          intro h_eq; apply h_not_gamma0; rw [← h_eq]; simp
        have := ((Fintype.equivFin γ) (F (thinBP_eab ⟨(i : ℕ) / Fintype.card α,
          thinBP_k_bound' F i⟩))).isLt
        omega⟩) := by
  dsimp [thinBP] at hs ⊢
  rw [LayeredBranchingProgram.evalLayer_succ]
  grind

theorem thinBP_CorrectState_succ {n} (x : α → β) :
    thinBP_CorrectState F n x (evalLayer (thinBP F) n x) := by
  induction n using Fin.inductionOn
  · exact thinBP_CorrectState_zero F x
  rename_i n ih
  by_cases h : n = 0
  · subst n
    rw [Fin.succ_zero_eq_one']
    exact thinBP_CorrectState_one F x
  let _ := @Classical.inhabited_of_nonempty α ‹_›
  have ha : 0 < Fintype.card α := by positivity
  have h_cond2 : 0 < Fintype.card β ^ Fintype.card α := by positivity
  have h_depth : 1 < (thinBP F).depth + 1 := by
    rw [thinBP_depth]
    rw [← Nat.add_one_le_iff] at ha h_cond2
    grw [← h_cond2, ← ha]
    norm_num
  have hn_val_ne : ¬(n.castSucc : Fin _).val = 0 := by
    intro heq; apply h; ext; simpa using heq
  unfold thinBP_CorrectState at ih ⊢
  rw [dif_neg (show (n.succ : Fin _).val ≠ 0 from by simp)] at ⊢
  rw [dif_neg hn_val_ne] at ih
  set a := Fintype.card α
  set b := Fintype.card β
  set c := Fintype.card γ
  haveI : NeZero c := ⟨(Fintype.card_pos_iff.mpr ⟨F (fun _ ↦ Classical.arbitrary β)⟩).ne'⟩
  set k_old := (n : ℕ) / a
  set pos_old := (n : ℕ) % a
  set k_new := ((n : ℕ) + 1) / a
  set pos_new := ((n : ℕ) + 1) % a
  have hn_lt : (n : ℕ) < a * b ^ a := by
    simpa only [thinBP_depth] using n.isLt
  have hk_old_bound : k_old < b ^ a := Nat.div_lt_of_lt_mul hn_lt
  -- Case split: boundary or not
  have h_dam : a * k_old + pos_old = (n : ℕ) := by
    have := Nat.div_add_mod (n : ℕ) a
    omega
  by_cases h_boundary : pos_old = a - 1
  · -- Boundary case: k_new = k_old + 1, pos_new = 0
    have h_eq : (n : ℕ) + 1 = a * (k_old + 1) := by
      have _ := mul_add a k_old 1
      omega
    have hk_new : k_new = k_old + 1 := by
      simp only [k_new]; rw [h_eq]; exact Nat.mul_div_cancel_left _ ha
    have hpos_new : pos_new = 0 := by
      simp only [pos_new]; rw [h_eq]
      exact Nat.mul_mod_right a (k_old + 1)
    clear h_eq
    dsimp only at ih ⊢
    split_ifs at ih with h_found h_k_lt h_match
    · split_ifs with h
      · convert thinBP_edge_inr' F n ( by aesop ) x ⟨ _, _ ⟩ ih using 1;
      · simp [Nat.succ_div, *] at h
        split_ifs at h
        · exact absurd h (by linarith! [Nat.mod_add_div n a, Nat.sub_add_cancel ha])
        · exact absurd h h_found.1.not_ge
      · simp [Nat.succ_div, *] at h
        split_ifs at h
        · exact absurd h (by linarith! [Nat.mod_add_div n a, Nat.sub_add_cancel ha])
        · · exact absurd h h_found.1.not_ge
      · grind only
    · -- Boundary, matching (.inl 0)
      have hi' : n.castSucc ≠ (0 : Fin _) := by intro heq; apply h; exact Fin.ext (by simpa using Fin.ext_iff.mp heq)
      have h_div_eq_b : ↑n.succ / Fintype.card α = k_old + 1 := by
        simp only [Fin.val_succ]; exact hk_new
      have h_mod_eq_zero_b : ↑n.succ % Fintype.card α = 0 := by
        simp only [Fin.val_succ]; exact hpos_new
      have h_pos_bound : ↑n.castSucc % Fintype.card α + 1 = Fintype.card α := by
        show pos_old + 1 = a; omega
      have h_pos_le : ↑n.castSucc % Fintype.card α + 1 ≤ Fintype.card α := le_of_eq h_pos_bound
      by_cases h_sym : x ((Fintype.equivFin α).symm ⟨↑n % Fintype.card α, Nat.mod_lt _ Fintype.card_pos⟩) =
        thinBP_eab (α := α) (β := β) ⟨↑n / Fintype.card α, thinBP_k_bound' F n⟩
          ((Fintype.equivFin α).symm ⟨↑n % Fintype.card α, Nat.mod_lt _ Fintype.card_pos⟩)
      · -- Last symbol matches → full string matches x = thinBP_eab k_old
        have h_match_ext : thinBP_match ⟨↑n.castSucc / Fintype.card α, h_k_lt⟩ (↑n.castSucc % Fintype.card α + 1) h_pos_le x :=
          (thinBP_match_succ _ _ _ x).mpr ⟨h_match, h_sym⟩
        have h_full_match : thinBP_match ⟨k_old, hk_old_bound⟩ (Fintype.card α) (le_refl _) x :=
          (thinBP_match_congr rfl h_pos_bound).mp h_match_ext
        have h_idx_eq : thinBP_index x = ⟨k_old, hk_old_bound⟩ :=
          (thinBP_match_card _ x).mp h_full_match
        by_cases h_gamma0 : F (thinBP_eab ⟨↑n / Fintype.card α, thinBP_k_bound' F n⟩) =
          (Fintype.equivFin γ).symm 0
        · -- F output = γ0 → stay at .inl 0
          have h_edge := thinBP_edge_inl0_match_boundary_gamma0' F n hi' x h_boundary h_sym h_gamma0 ih
          have h_fx_eq : F x = (Fintype.equivFin γ).symm 0 := by
            have hx : x = thinBP_eab ⟨k_old, hk_old_bound⟩ := by
              rw [← Equiv.symm_apply_eq]; exact h_idx_eq
            rw [hx]; exact h_gamma0
          have h_not_found_new : ¬(↑(thinBP_index x) < ↑n.succ / Fintype.card α ∧ F x ≠ (Fintype.equivFin γ).symm 0) := by
            push_neg; intro _; exact h_fx_eq
          split_ifs with g1 g2 g3
          · exact absurd g1 h_not_found_new
          · exact h_edge
          · exfalso; apply g3
            intro j; exact absurd j.isLt (by have := h_mod_eq_zero_b; omega)
          · exact h_edge
        · -- F output ≠ γ0 → go to .inr
          have h_edge := thinBP_edge_inl0_match_boundary_not_gamma0' F n hi' x h_boundary h_sym h_gamma0 ih
          have h_found_new : ↑(thinBP_index x) < ↑n.succ / Fintype.card α ∧ F x ≠ (Fintype.equivFin γ).symm 0 := by
            refine ⟨?_, ?_⟩
            · rw [h_div_eq_b]; simp only [h_idx_eq, Fin.val_mk]; omega
            · intro h_eq; apply h_gamma0
              have hx : x = thinBP_eab ⟨k_old, hk_old_bound⟩ := by
                rw [← Equiv.symm_apply_eq]; exact h_idx_eq
              rw [← hx]; exact h_eq
          have hx : x = thinBP_eab ⟨k_old, hk_old_bound⟩ := by
            rw [← Equiv.symm_apply_eq]; exact h_idx_eq
          split_ifs with g1
          · have : F x = F (thinBP_eab ⟨↑n / Fintype.card α, thinBP_k_bound' F n⟩) := by rw [hx]
            convert h_edge using 1; simp [this]
          · exact absurd h_found_new g1
      · -- Last symbol doesn't match → reset to .inl 0
        have h_edge := thinBP_edge_inl0_nomatch_boundary' F n hi' x h_boundary h_sym ih
        have h_no_full_match : ¬thinBP_match ⟨↑n.castSucc / Fintype.card α, h_k_lt⟩ (↑n.castSucc % Fintype.card α + 1) h_pos_le x := by
          rw [thinBP_match_succ]; push_neg; intro _; exact h_sym
        have h_idx_ne : (thinBP_index x : ℕ) ≠ k_old := by
          intro h_eq; apply h_no_full_match
          exact (thinBP_match_congr rfl h_pos_bound.symm).mp ((thinBP_match_card _ x).mpr (Fin.ext h_eq))
        have h_not_found_new : ¬(↑(thinBP_index x) < ↑n.succ / Fintype.card α ∧ F x ≠ (Fintype.equivFin γ).symm 0) := by
          push_neg at h_found ⊢; intro h_lt; rw [h_div_eq_b] at h_lt
          exact h_found (show (↑(thinBP_index x) : ℕ) < k_old from by omega)
        split_ifs with g1 g2 g3
        · exact absurd g1 h_not_found_new
        · exact h_edge
        · exfalso; apply g3
          intro j; exact absurd j.isLt (by have := h_mod_eq_zero_b; omega)
        · exact h_edge
    · -- Boundary, not matching (.inl 1) → reset to .inl 0
      have hi' : n.castSucc ≠ (0 : Fin _) := by intro heq; apply h; exact Fin.ext (by simpa using Fin.ext_iff.mp heq)
      have h_edge := thinBP_edge_inl1_boundary' F n hi' x h_boundary ih
      have h_div_eq : ↑n.succ / Fintype.card α = k_old + 1 := by
        simp only [Fin.val_succ]; exact hk_new
      have h_mod_eq_zero : ↑n.succ % Fintype.card α = 0 := by
        simp only [Fin.val_succ]; exact hpos_new
      -- Show h_found stays false: if idx < k_old+1 and F x ≠ γ0, then idx < k_old (since idx ≠ k_old)
      -- idx = k_old would mean full match, contradicting h_match
      have h_idx_ne : (thinBP_index x : ℕ) ≠ k_old := by
        intro h_eq
        apply h_match
        have h_full := (thinBP_match_card (α := α) (β := β) ⟨k_old, hk_old_bound⟩ x).mpr (Fin.ext h_eq)
        exact fun j => h_full ⟨j.val, by have := j.isLt; have := Nat.mod_lt (↑n.castSucc) (Fintype.card_pos (α := α)); omega⟩
      have h_not_found_new : ¬(↑(thinBP_index x) < ↑n.succ / Fintype.card α ∧ F x ≠ (Fintype.equivFin γ).symm 0) := by
        push_neg at h_found ⊢
        intro h_lt
        rw [h_div_eq] at h_lt
        have h_lt_old : (↑(thinBP_index x) : ℕ) < k_old := by omega
        exact h_found h_lt_old
      split_ifs with g1 g2 g3
      · exact absurd g1 h_not_found_new
      · exact h_edge
      · exfalso; apply g3
        intro j; exact absurd j.isLt (by have := h_mod_eq_zero; omega)
      · exact h_edge
    · exact absurd hk_old_bound h_k_lt
  · have hpos_lt : pos_old + 1 < a := by
      have := Nat.mod_lt (n : ℕ) ha; omega
    have hk_new_eq : k_new = k_old := by
      simp only [k_new]
      have h_rewrite : (↑n + 1 : ℕ) = (↑n % a + 1) + a * (↑n / a) := by linarith [Nat.div_add_mod (↑n : ℕ) a]
      conv_lhs => rw [h_rewrite]
      rw [Nat.add_mul_div_left _ _ ha, Nat.div_eq_of_lt hpos_lt, Nat.zero_add]
    have hpos_new_eq : pos_new = pos_old + 1 := by
      simp only [pos_new]
      have h_rewrite : (↑n + 1 : ℕ) = (↑n % a + 1) + a * (↑n / a) := by linarith [Nat.div_add_mod (↑n : ℕ) a]
      conv_lhs => rw [h_rewrite]
      rw [Nat.add_mul_mod_self_left]
      exact Nat.mod_eq_of_lt hpos_lt
    dsimp only at ih ⊢
    split_ifs at ih with h_found h_k_lt h_match
    -- Non-boundary found (.inr)
    · have hi' : n.castSucc ≠ (0 : Fin _) := by intro heq; apply h; exact Fin.ext (by simpa using Fin.ext_iff.mp heq)
      simp only [Fin.val_succ] at *
      split_ifs with g1
      · exact thinBP_edge_inr' F n hi' x ⟨_, _⟩ ih
      all_goals (exfalso; apply g1; refine ⟨?_, h_found.2⟩; rw [show ((n : ℕ) + 1) / a = k_old from hk_new_eq]; exact h_found.1)
    -- Non-boundary matching (.inl 0)
    · have hi' : n.castSucc ≠ (0 : Fin _) := by intro heq; apply h; exact Fin.ext (by simpa using Fin.ext_iff.mp heq)
      have h_div_eq : ↑n.succ / Fintype.card α = ↑n.castSucc / Fintype.card α := by
        simp only [Fin.val_succ, Fin.coe_castSucc]; exact hk_new_eq
      have h_mod_eq : ↑n.succ % Fintype.card α = ↑n.castSucc % Fintype.card α + 1 := by
        simp only [Fin.val_succ, Fin.coe_castSucc]; exact hpos_new_eq
      by_cases h_sym : x ((Fintype.equivFin α).symm ⟨↑n % Fintype.card α, Nat.mod_lt _ Fintype.card_pos⟩) =
        thinBP_eab (α := α) (β := β) ⟨↑n / Fintype.card α, thinBP_k_bound' F n⟩
          ((Fintype.equivFin α).symm ⟨↑n % Fintype.card α, Nat.mod_lt _ Fintype.card_pos⟩)
      · -- Symbol matches → edge stays .inl 0, match extends to pos_old + 1
        have h_edge := thinBP_edge_inl0_match_interior' F n hi' x h_boundary h_sym ih
        have h_match_ext : thinBP_match ⟨↑n.castSucc / Fintype.card α, h_k_lt⟩ (↑n.castSucc % Fintype.card α + 1) (le_of_lt hpos_lt) x :=
          (thinBP_match_succ _ _ _ x).mpr ⟨h_match, h_sym⟩
        split_ifs with g1 g2 g3
        · grind only
        · exact h_edge
        · exfalso
          apply g3
          exact (thinBP_match_congr (Fin.ext h_div_eq.symm) h_mod_eq.symm).mp h_match_ext
        · grind only
      · -- Symbol doesn't match → edge goes .inl 1, match fails at pos_old + 1
        have h_edge := thinBP_edge_inl0_nomatch_interior' F n hi' x h_boundary h_sym ih
        have h_match_fail : ¬thinBP_match ⟨↑n.castSucc / Fintype.card α, h_k_lt⟩ (↑n.castSucc % Fintype.card α + 1) (le_of_lt hpos_lt) x := by
          rw [thinBP_match_succ]
          push_neg
          intro
          exact h_sym
        split_ifs with g1 g2 g3
        · grind only
        · exfalso; apply h_match_fail
          exact (thinBP_match_congr (Fin.ext h_div_eq.symm) h_mod_eq.symm).mpr g3
        · exact h_edge
        · grind only
    -- Non-boundary not matching (.inl 1)
    · have hi' : n.castSucc ≠ (0 : Fin _) := by intro heq; apply h; exact Fin.ext (by simpa using Fin.ext_iff.mp heq)
      have h_edge := thinBP_edge_inl1_interior' F n hi' x h_boundary ih
      have h_div_eq : ↑n.succ / Fintype.card α = ↑n.castSucc / Fintype.card α := by
        simp only [Fin.val_succ, Fin.coe_castSucc]; exact hk_new_eq
      have h_mod_eq : ↑n.succ % Fintype.card α = ↑n.castSucc % Fintype.card α + 1 := by
        simp only [Fin.val_succ, Fin.coe_castSucc]; exact hpos_new_eq
      split_ifs with g1 g2 g3
      · grind only
      · exfalso
        apply h_match
        have hfin : (⟨↑n.castSucc / Fintype.card α, h_k_lt⟩ : Fin _) = ⟨↑n.succ / Fintype.card α, g2⟩ :=
          Fin.ext h_div_eq.symm
        rw [hfin]
        have g3' : thinBP_match ⟨↑n.succ / Fintype.card α, g2⟩ (↑n.castSucc % Fintype.card α + 1) (le_of_lt hpos_lt) x :=
          (thinBP_match_congr rfl h_mod_eq).mp g3
        exact ((thinBP_match_succ _ _ _ x).mp g3').1
      · exact h_edge
      · grind only
    · exact absurd hk_old_bound h_k_lt

theorem thinBP_computes : (thinBP F).computes F := by
  intro x
  rw [eval]
  have h := thinBP_CorrectState_succ F (n := .last _) x
  have h_ge : Fintype.card β ^ Fintype.card α ≤ (thinBP F).depth / Fintype.card α := by
    simp [thinBP]
  simp [thinBP_CorrectState, (thinBP_depth_pos F).out, h_ge.not_gt] at h
  split at h
  · rename_i h₂
    rw [cast_comm] at h
    rw [h]
    simp only [thinBP, eq_mp_eq_cast, cast_cast, cast_eq]
    rw! [Nat.sub_one_add_one]
    · simp
    replace h₂ := h₂.right
    contrapose! h₂
    rw [Equiv.eq_symm_apply]
    have _ : Nonempty γ := ⟨F (fun _ ↦ Nonempty.some ‹_›)⟩
    exact Fin.val_eq_zero_iff.mp h₂
  · rename_i h₂
    push_neg at h₂
    rw [cast_comm] at h
    rw [h]
    have h' : Fin.last (Fintype.card α * Fintype.card β ^ Fintype.card α) ≠ 0 := by
      simp
    simp only [thinBP, eq_mp_eq_cast, cast_cast, cast_eq, h', reduceDIte]
    rw [h₂]
    exact Fin.val_lt_of_le (thinBP_index x) h_ge

end thinBP_proof
------------

/-- Every function can be computed by an oblivious branching program
of exponential size and constant width. -/
theorem computes_const_width :
    ∃ (P : LayeredBranchingProgram α β γ) (_ : P.Finite),
      P.computes F ∧
      P.IsOblivious ∧
      P.width = Fintype.card γ + 1 ∧
      P.depth = Fintype.card α * (Fintype.card β ^ Fintype.card α) := by
  have _ : Nonempty γ := ⟨ F (fun _ ↦ Nonempty.some ‹_›) ⟩
  use thinBP F, thinBP_Finite F
  and_intros
  · exact thinBP_computes F
  · exact thinBP_IsOblivious F
  · rw [thinBP_width]
  · rfl

/-- A boolean function can be computed in O(n * 2^n) depth and width 3.-/
theorem computes_bool_width_3 (F : (α → Bool) → Bool) :
    ∃ (P : LayeredBranchingProgram α Bool Bool) (_ : P.Finite),
      P.computes F ∧
      P.IsOblivious ∧
      P.width = 3 ∧
      P.depth = Fintype.card α * 2 ^ Fintype.card α :=
  computes_const_width F
