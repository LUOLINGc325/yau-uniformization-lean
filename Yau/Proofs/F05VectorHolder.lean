import Yau.LeafProofs.L16

/-! An actual closed Banach graph for vector-valued parabolic Hölder functions. -/

open Filter Set
open scoped Topology
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency.types false

namespace Yau.Proofs.F05Aux

open Yau.Parabolic Yau.LeafProofs.L16Aux

variable {n : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

def vectorHolderGraph (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
    (α : ℝ) (Q : Set (Point n)) :
    Submodule ℝ (BoundedContinuousFunction Q V × BoundedContinuousFunction (HolderPairs Q) V) where
  carrier := {u | ∀ z : HolderPairs Q,
    u.1 z.val.1 - u.1 z.val.2 = holderWeight α z.val.1.val z.val.2.val • u.2 z}
  zero_mem' := by intro z; simp
  add_mem' := by
    intro u v hu hv z
    change (u.1 z.val.1 + v.1 z.val.1) - (u.1 z.val.2 + v.1 z.val.2) =
      holderWeight α z.val.1.val z.val.2.val • (u.2 z + v.2 z)
    rw [smul_add, ← hu z, ← hv z]
    abel
  smul_mem' := by
    intro a u hu z
    change a • u.1 z.val.1 - a • u.1 z.val.2 =
      holderWeight α z.val.1.val z.val.2.val • (a • u.2 z)
    rw [← smul_sub, hu z, smul_comm]

theorem vectorHolderGraph_isClosed (α : ℝ) (Q : Set (Point n)) :
    IsClosed (vectorHolderGraph V α Q :
      Set (BoundedContinuousFunction Q V × BoundedContinuousFunction (HolderPairs Q) V)) := by
  change IsClosed {u : BoundedContinuousFunction Q V × BoundedContinuousFunction (HolderPairs Q) V |
    ∀ z : HolderPairs Q,
      u.1 z.val.1 - u.1 z.val.2 = holderWeight α z.val.1.val z.val.2.val • u.2 z}
  simp only [Set.ofPred_forall]
  apply isClosed_iInter
  intro z
  exact isClosed_eq
    (((BoundedContinuousFunction.evalCLM ℝ z.val.1).continuous.comp continuous_fst).sub
      ((BoundedContinuousFunction.evalCLM ℝ z.val.2).continuous.comp continuous_fst))
    (continuous_const.smul ((BoundedContinuousFunction.evalCLM ℝ z).continuous.comp continuous_snd))

instance vectorHolderGraph_completeSpace [CompleteSpace V] (α : ℝ) (Q : Set (Point n)) :
    CompleteSpace (vectorHolderGraph V α Q) :=
  (vectorHolderGraph_isClosed (V := V) α Q).completeSpace_coe

def vectorHolderFun {α : ℝ} {Q : Set (Point n)} (u : vectorHolderGraph V α Q) : Point n → V := by
  classical
  exact fun p => if hp : p ∈ Q then u.val.1 ⟨p,hp⟩ else 0

theorem vectorHolderFun_apply {α : ℝ} {Q : Set (Point n)}
    (u : vectorHolderGraph V α Q) (p : Q) : vectorHolderFun u p.val = u.val.1 p := by
  simp [vectorHolderFun, p.property]

theorem vectorHolderFun_zero {α : ℝ} {Q : Set (Point n)} :
    vectorHolderFun (0 : vectorHolderGraph V α Q) = 0 := by
  classical
  funext p
  by_cases hp : p ∈ Q <;> simp [vectorHolderFun, hp]

theorem vectorHolderFun_add {α : ℝ} {Q : Set (Point n)}
    (u v : vectorHolderGraph V α Q) :
    vectorHolderFun (u + v) = vectorHolderFun u + vectorHolderFun v := by
  classical
  funext p
  by_cases hp : p ∈ Q <;> simp [vectorHolderFun, hp]

theorem vectorHolderFun_smul {α : ℝ} {Q : Set (Point n)} (a : ℝ)
    (u : vectorHolderGraph V α Q) : vectorHolderFun (a • u) = a • vectorHolderFun u := by
  classical
  funext p
  by_cases hp : p ∈ Q <;> simp [vectorHolderFun, hp]

theorem vectorHolderFun_eval_continuous {α : ℝ} {Q : Set (Point n)} (p : Point n) :
    Continuous (fun u : vectorHolderGraph V α Q => vectorHolderFun u p) := by
  classical
  by_cases hp : p ∈ Q
  · simpa [vectorHolderFun, hp, BoundedContinuousFunction.evalCLM, Function.comp_def] using
      (BoundedContinuousFunction.evalCLM ℝ (⟨p,hp⟩ : Q)).continuous.comp
        (continuous_fst.comp continuous_subtype_val)
  · simpa only [vectorHolderFun, dite_eq_right hp] using
      (continuous_const : Continuous (fun _ : vectorHolderGraph V α Q => (0 : V)))

theorem vectorHolderFun_holderBound {α : ℝ} {Q : Set (Point n)}
    (u : vectorHolderGraph V α Q) : HolderBound α Q (vectorHolderFun u) ‖u‖ := by
  have hN1 : ‖u.val.1‖ ≤ ‖u‖ := le_max_left _ _
  have hN2 : ‖u.val.2‖ ≤ ‖u‖ := le_max_right _ _
  refine ⟨norm_nonneg _, ?_, ?_⟩
  · intro p hp
    rw [vectorHolderFun_apply u ⟨p,hp⟩]
    exact (u.val.1.norm_coe_le_norm ⟨p,hp⟩).trans hN1
  · intro p hp q hq
    by_cases hpq : p = q
    · subst q
      simp only [sub_self, norm_zero]
      exact mul_nonneg (norm_nonneg _) (by dsimp [holderWeight]; positivity)
    let z : HolderPairs Q := ⟨(⟨p,hp⟩,⟨q,hq⟩), fun h => hpq (congrArg Subtype.val h)⟩
    have heq : vectorHolderFun u p - vectorHolderFun u q = holderWeight α p q • u.val.2 z := by
      simpa only [vectorHolderFun_apply u ⟨p,hp⟩, vectorHolderFun_apply u ⟨q,hq⟩] using u.property z
    have hW : 0 < holderWeight α p q := holderWeight_pos_of_ne α hpq
    rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos hW]
    exact ((mul_le_mul_of_nonneg_left (u.val.2.norm_coe_le_norm z) hW.le).trans
      (mul_le_mul_of_nonneg_left hN2 hW.le)).trans_eq (mul_comm _ _)

theorem vectorHolderGraph_ext {α : ℝ} {Q : Set (Point n)}
    {u v : vectorHolderGraph V α Q} (h : ∀ p : Q, u.val.1 p = v.val.1 p) : u = v := by
  apply Subtype.ext
  apply Prod.ext
  · exact BoundedContinuousFunction.ext h
  · apply BoundedContinuousFunction.ext
    intro z
    apply smul_right_injective V (holderPair_weight_pos α z).ne'
    change holderWeight α z.val.1.val z.val.2.val • u.val.2 z =
      holderWeight α z.val.1.val z.val.2.val • v.val.2 z
    rw [← u.property z, ← v.property z, h z.val.1, h z.val.2]

def boundedVectorContinuousOfBound {Z : Type*} [TopologicalSpace Z] (f : Z → V)
    (hc : Continuous f) (C : ℝ) (hC : ∀ z, ‖f z‖ ≤ C) : BoundedContinuousFunction Z V :=
  BoundedContinuousFunction.mkOfBound ⟨f,hc⟩ (2*C) (by
    intro z w
    rw [dist_eq_norm]
    exact (norm_sub_le (f z) (f w)).trans (by linarith [hC z,hC w]))

theorem vectorHolderQuotient_continuous {α C : ℝ} {Q : Set (Point n)} {f : Point n → V}
    (hα : 0 < α) (hf : HolderBound α Q f C) :
    Continuous (fun z : HolderPairs Q =>
      (holderWeight α z.val.1.val z.val.2.val)⁻¹ • (f z.val.1.val - f z.val.2.val)) := by
  have h1 : Continuous (fun z : HolderPairs Q => z.val.1) :=
    continuous_fst.comp continuous_subtype_val
  have h2 : Continuous (fun z : HolderPairs Q => z.val.2) :=
    continuous_snd.comp continuous_subtype_val
  have hval : Continuous (fun p : Q => (p.val : Point n)) := continuous_subtype_val
  have hx : Continuous (fun z : HolderPairs Q => z.val.1.val.1 - z.val.2.val.1) :=
    (hval.comp h1).fst.sub (hval.comp h2).fst
  have ht : Continuous (fun z : HolderPairs Q => z.val.1.val.2 - z.val.2.val.2) :=
    (hval.comp h1).snd.sub (hval.comp h2).snd
  have hW : Continuous (fun z : HolderPairs Q => holderWeight α z.val.1.val z.val.2.val) := by
    unfold holderWeight
    exact (hx.norm.rpow_const (fun _ => Or.inr hα.le)).add
      (ht.abs.rpow_const (fun _ => Or.inr (by positivity : 0 ≤ α/2)))
  have hFc : Continuous (fun p : Q => f p.val) := (holderBound_continuousOn hα hf).domRestrict
  exact (hW.inv₀ (fun z => (holderPair_weight_pos α z).ne')).smul
    ((hFc.comp h1).sub (hFc.comp h2))

theorem vectorHolderQuotient_norm_bound {α C : ℝ} {Q : Set (Point n)} {f : Point n → V}
    (hf : HolderBound α Q f C) (z : HolderPairs Q) :
    ‖(holderWeight α z.val.1.val z.val.2.val)⁻¹ • (f z.val.1.val - f z.val.2.val)‖ ≤ C := by
  have hW := holderPair_weight_pos α z
  calc
    _ = ‖f z.val.1.val - f z.val.2.val‖ / holderWeight α z.val.1.val z.val.2.val := by
      rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hW]
      ring
    _ ≤ C := (div_le_iff₀ hW).mpr
      (hf.2.2 z.val.1.val z.val.1.property z.val.2.val z.val.2.property)

def vectorHolderGraphOfBound {α C : ℝ} {Q : Set (Point n)} {f : Point n → V}
    (hα : 0 < α) (hf : HolderBound α Q f C) : vectorHolderGraph V α Q :=
  ⟨(boundedVectorContinuousOfBound (fun p : Q => f p.val)
      (holderBound_continuousOn hα hf).domRestrict C (fun p => hf.2.1 p.val p.property),
    boundedVectorContinuousOfBound (fun z : HolderPairs Q =>
      (holderWeight α z.val.1.val z.val.2.val)⁻¹ • (f z.val.1.val - f z.val.2.val))
      (vectorHolderQuotient_continuous hα hf) C (vectorHolderQuotient_norm_bound hf)), by
    intro z
    change f z.val.1.val - f z.val.2.val =
      holderWeight α z.val.1.val z.val.2.val •
        ((holderWeight α z.val.1.val z.val.2.val)⁻¹ • (f z.val.1.val - f z.val.2.val))
    rw [smul_smul, mul_inv_cancel₀ (holderPair_weight_pos α z).ne', one_smul]⟩

theorem vectorHolderGraphOfBound_norm_le {α C : ℝ} {Q : Set (Point n)} {f : Point n → V}
    (hα : 0 < α) (hf : HolderBound α Q f C) : ‖vectorHolderGraphOfBound hα hf‖ ≤ C := by
  change max ‖(vectorHolderGraphOfBound hα hf).val.1‖
    ‖(vectorHolderGraphOfBound hα hf).val.2‖ ≤ C
  apply max_le
  · apply (BoundedContinuousFunction.norm_le hf.1).mpr
    intro p
    exact hf.2.1 p.val p.property
  · apply (BoundedContinuousFunction.norm_le hf.1).mpr
    exact vectorHolderQuotient_norm_bound hf

theorem vectorHolderGraphOfBound_eqOn {α C : ℝ} {Q : Set (Point n)} {f : Point n → V}
    (hα : 0 < α) (hf : HolderBound α Q f C) :
    EqOn (vectorHolderFun (vectorHolderGraphOfBound hα hf)) f Q := by
  intro p hp
  rw [vectorHolderFun_apply _ ⟨p,hp⟩]
  rfl

end Yau.Proofs.F05Aux
