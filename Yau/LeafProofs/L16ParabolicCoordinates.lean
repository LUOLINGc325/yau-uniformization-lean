import Yau.LeafProofs.L16WeakMollification
import Yau.LeafProofs.L16WeakJetMollification
import Mathlib.MeasureTheory.Measure.Haar.Disintegration

/-!
# Actual real coordinates for parabolic weak jets

The real and imaginary spatial basis vectors, together with the time vector,
are transported to the usual basis of a finite real product. The change of
Lebesgue measure is obtained from Haar uniqueness, with a finite positive factor.
-/

open MeasureTheory
open scoped Topology ContDiff
noncomputable section
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic

set_option backward.isDefEq.respectTransparency false

/-- Every real spatial direction and the time direction. -/
abbrev ParabolicJointIdx (n : ℕ) := Yau.RIdx n ⊕ Unit

/-- The genuine spatial real/imaginary vectors and the genuine time vector. -/
def parabolicJointVec {n : ℕ} : ParabolicJointIdx n → Point n
  | .inl i => (Yau.realVec i, 0)
  | .inr _ => (0, 1)

/-- A finite enumeration; no dimension arithmetic is needed. -/
def parabolicJointIndexEquiv (n : ℕ) :
    ParabolicJointIdx n ≃ Fin (Fintype.card (ParabolicJointIdx n)) :=
  Fintype.equivFin _

private def parabolicJointLinearEquiv (n : ℕ) :
    Point n ≃ₗ[ℝ] (ParabolicJointIdx n → ℝ) where
  toFun p := Sum.elim ((spaceRealBasis n).toBasis.equivFun p.1) (fun _ => p.2)
  invFun r := ((spaceRealBasis n).toBasis.equivFun.symm (fun i => r (.inl i)), r (.inr ()))
  left_inv p := by simp
  right_inv r := by
    funext j
    cases j with
    | inl i => simp
    | inr t => cases t; rfl
  map_add' p q := by
    funext j
    cases j <;> simp
  map_smul' a p := by
    funext j
    cases j <;> simp

/-- The actual continuous real linear equivalence from parabolic points to a
finite product of real coordinate lines. -/
def parabolicCoordinateEquiv (n : ℕ) :
    Point n ≃L[ℝ] (Fin (Fintype.card (ParabolicJointIdx n)) → ℝ) :=
  ((parabolicJointLinearEquiv n).trans
    (LinearEquiv.piCongrLeft ℝ (fun _ => ℝ) (parabolicJointIndexEquiv n))).toContinuousLinearEquiv

private theorem parabolicCoordinateEquiv_apply_index {n : ℕ} (p : Point n)
    (j : ParabolicJointIdx n) :
    parabolicCoordinateEquiv n p (parabolicJointIndexEquiv n j) =
      parabolicJointLinearEquiv n p j := by
  simp [parabolicCoordinateEquiv, LinearEquiv.piCongrLeft, LinearEquiv.piCongrLeft']

@[simp] theorem parabolicCoordinateEquiv_spatial {n : ℕ} (p : Point n) (i : Yau.RIdx n) :
    parabolicCoordinateEquiv n p (parabolicJointIndexEquiv n (.inl i)) =
      Yau.realCoord p.1 i := by
  rw [parabolicCoordinateEquiv_apply_index]
  change (spaceRealBasis n).toBasis.equivFun p.1 i = _
  rw [Module.Basis.equivFun_apply, (spaceRealBasis n).coe_toBasis_repr_apply,
    (spaceRealBasis n).repr_apply_apply, spaceRealBasis_apply, real_inner_comm,
    real_inner_realVec]

@[simp] theorem parabolicCoordinateEquiv_time {n : ℕ} (p : Point n) :
    parabolicCoordinateEquiv n p (parabolicJointIndexEquiv n (.inr ())) = p.2 := by
  rw [parabolicCoordinateEquiv_apply_index]
  rfl

/-- Each specified actual direction maps to its corresponding coordinate vector. -/
@[simp] theorem parabolicCoordinateEquiv_jointVec {n : ℕ} (j : ParabolicJointIdx n) :
    parabolicCoordinateEquiv n (parabolicJointVec j) =
      Pi.single (parabolicJointIndexEquiv n j) 1 := by
  classical
  ext k
  obtain ⟨i, rfl⟩ := (parabolicJointIndexEquiv n).surjective k
  rw [parabolicCoordinateEquiv_apply_index]
  cases j with
  | inl a =>
      cases i with
      | inl b =>
          change (spaceRealBasis n).toBasis.equivFun (Yau.realVec a) b = _
          rw [← spaceRealBasis_apply n a, ← OrthonormalBasis.coe_toBasis,
            Module.Basis.equivFun_self]
          simp [Pi.single_apply, eq_comm]
      | inr b => simp [parabolicJointLinearEquiv, parabolicJointVec]
  | inr a =>
      cases i with
      | inl b => simp [parabolicJointLinearEquiv, parabolicJointVec]
      | inr b => cases a; cases b; simp [parabolicJointLinearEquiv, parabolicJointVec]

/-- The actual derivative chain rule in each specified basis direction. -/
theorem fderiv_comp_parabolicCoordinateEquiv_jointVec {n : ℕ}
    {φ : (Fin (Fintype.card (ParabolicJointIdx n)) → ℝ) → ℝ}
    (hφ : Differentiable ℝ φ) (p : Point n) (j : ParabolicJointIdx n) :
    fderiv ℝ (φ ∘ parabolicCoordinateEquiv n) p (parabolicJointVec j) =
      fderiv ℝ φ (parabolicCoordinateEquiv n p)
        (Pi.single (parabolicJointIndexEquiv n j) 1) := by
  rw [fderiv_comp p (hφ _) (parabolicCoordinateEquiv n).differentiableAt,
    ContinuousLinearEquiv.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    parabolicCoordinateEquiv_jointVec]

/-- Haar uniqueness supplies an honest, strictly positive, finite change of
measure constant for the actual linear coordinate equivalence. -/
theorem parabolicCoordinateEquiv_map_volume (n : ℕ) :
    ∃ c : ℝ, 0 < c ∧
      Measure.map (parabolicCoordinateEquiv n) (volume : Measure (Point n)) =
        ENNReal.ofReal c •
          (volume : Measure (Fin (Fintype.card (ParabolicJointIdx n)) → ℝ)) := by
  let e := parabolicCoordinateEquiv n
  let μ := Measure.map e (volume : Measure (Point n))
  have : μ.IsAddHaarMeasure := e.isAddHaarMeasure_map volume
  let c := Measure.addHaarScalarFactor μ volume
  have hc : 0 < c := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure μ volume
  refine ⟨(c : ℝ), hc, ?_⟩
  simpa only [ENNReal.ofReal_coe_nnreal, ENNReal.smul_def] using
    (Measure.isAddLeftInvariant_eq_smul μ volume)


/-- Proper global L² membership is preserved by the actual change of coordinates. -/
theorem memLp_comp_parabolicCoordinateEquiv_symm {n : ℕ} {f : Point n → ℝ}
    (hf : MemLp f 2 volume) :
    MemLp (f ∘ (parabolicCoordinateEquiv n).symm) 2 volume := by
  let e := parabolicCoordinateEquiv n
  obtain ⟨c, hc, hmap⟩ := parabolicCoordinateEquiv_map_volume n
  have h0 : ENNReal.ofReal c ≠ 0 := (ENNReal.ofReal_pos.mpr hc).ne'
  have h : MemLp (f ∘ e.symm) 2 (Measure.map e (volume : Measure (Point n))) :=
    e.toHomeomorph.toMeasurableEquiv.memLp_map_measure_iff.mpr (by
      simpa only [Function.comp_def, Homeomorph.toMeasurableEquiv_coe,
        ContinuousLinearEquiv.coe_toHomeomorph, ContinuousLinearEquiv.symm_apply_apply] using hf)
  rw [hmap] at h
  have h' := h.smul_measure (ENNReal.inv_ne_top.mpr h0)
  simpa only [smul_smul, ENNReal.inv_mul_cancel h0 ENNReal.ofReal_ne_top, one_smul] using h'

/-- The literal change of variables, including its positive volume factor.
This identity also holds for the totalized Bochner integral. -/
theorem parabolicCoordinateEquiv_integral {n : ℕ} {c : ℝ} (hc : 0 < c)
    (hmap : Measure.map (parabolicCoordinateEquiv n) (volume : Measure (Point n)) =
      ENNReal.ofReal c •
        (volume : Measure (Fin (Fintype.card (ParabolicJointIdx n)) → ℝ)))
    (f : Point n → ℝ) :
    (∫ p, f p) = c * (∫ x, f ((parabolicCoordinateEquiv n).symm x)) := by
  have h := integral_map_equiv (μ := (volume : Measure (Point n)))
    (parabolicCoordinateEquiv n).toHomeomorph.toMeasurableEquiv
    (f ∘ (parabolicCoordinateEquiv n).symm)
  simp only [Homeomorph.toMeasurableEquiv_coe, ContinuousLinearEquiv.coe_toHomeomorph] at h
  rw [hmap, integral_smul_measure, ENNReal.toReal_ofReal hc.le, smul_eq_mul] at h
  simpa only [Function.comp_def, ContinuousLinearEquiv.symm_apply_apply] using h.symm

/-- A concrete finite graph of compact L² weak derivatives in all genuine
spatial real/imaginary directions and in time. -/
def FiniteParabolicWeakJet {n : ℕ} (N : ℕ) (u : Point n → ℝ)
    (U : List (ParabolicJointIdx n) → Point n → ℝ) : Prop :=
  U [] = u ∧
  (∀ v, v.length ≤ N → MemLp (U v) 2 volume ∧ HasCompactSupport (U v)) ∧
  ∀ v, v.length < N → ∀ j : ParabolicJointIdx n, ∀ φ : Point n → ℝ,
    ContDiff ℝ ∞ φ → HasCompactSupport φ →
    (∫ p, U v p * fderiv ℝ φ p (parabolicJointVec j)) =
      -(∫ p, U (j :: v) p * φ p)

/-- The concrete finite parabolic weak jet transports to the actual coordinate
weak jet, using the chain rule and cancellation of the positive Haar factor. -/
theorem finiteParabolicWeakJet_to_coordinate {n N : ℕ} {u : Point n → ℝ}
    {U : List (ParabolicJointIdx n) → Point n → ℝ}
    (hU : FiniteParabolicWeakJet N u U) :
    FiniteCoordinateWeakJet N (u ∘ (parabolicCoordinateEquiv n).symm)
      (fun w => U (w.map (parabolicJointIndexEquiv n).symm) ∘
        (parabolicCoordinateEquiv n).symm) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa only [List.map_nil] using congrArg
      (fun f : Point n → ℝ => f ∘ (parabolicCoordinateEquiv n).symm) hU.1
  · intro w hw
    have h := hU.2.1 (w.map (parabolicJointIndexEquiv n).symm) (by simpa using hw)
    exact ⟨memLp_comp_parabolicCoordinateEquiv_symm h.1,
      h.2.comp_homeomorph (parabolicCoordinateEquiv n).symm.toHomeomorph⟩
  · intro w hw i ψ hψ hcψ
    obtain ⟨c, hc, hmap⟩ := parabolicCoordinateEquiv_map_volume n
    have h := hU.2.2 (w.map (parabolicJointIndexEquiv n).symm) (by simpa using hw)
      ((parabolicJointIndexEquiv n).symm i) (ψ ∘ parabolicCoordinateEquiv n)
      (hψ.comp (parabolicCoordinateEquiv n).contDiff)
      (hcψ.comp_homeomorph (parabolicCoordinateEquiv n).toHomeomorph)
    simp only [fderiv_comp_parabolicCoordinateEquiv_jointVec
      (hψ.differentiable (by simp)), Equiv.apply_symm_apply, Function.comp_apply] at h
    rw [parabolicCoordinateEquiv_integral hc hmap,
      parabolicCoordinateEquiv_integral hc hmap] at h
    simp only [ContinuousLinearEquiv.apply_symm_apply] at h
    simp only [List.map_cons, Function.comp_apply]
    nlinarith

end Yau.LeafProofs.L16Aux
