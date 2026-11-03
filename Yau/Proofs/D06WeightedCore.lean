import Yau.Proofs.D06WeightedForm

/-! A separate carrier for the weighted Hardy norm. The original coefficient
space retains its ordinary norm throughout. -/

open scoped ComplexOrder
open MeasureTheory

noncomputable section
namespace Yau.NodeProofs.D06Aux

abbrev WeightedHardySeq (r : ℕ) := WithLp 0 (HardySeq r)

def weightedUnwrap {r : ℕ} : WeightedHardySeq r ≃ₗ[ℂ] HardySeq r :=
  WithLp.linearEquiv 0 ℂ (HardySeq r)

def weightedUnwrapLM {r : ℕ} : WeightedHardySeq r →ₗ[ℂ] HardySeq r :=
  (weightedUnwrap (r := r)).toLinearMap

def weightedWrapLM {r : ℕ} : HardySeq r →ₗ[ℂ] WeightedHardySeq r :=
  (weightedUnwrap (r := r)).symm.toLinearMap

variable {r : ℕ}
variable (L : HardyCircle → Matrix (Fin r) (Fin r) ℂ)
variable (hLp : ∀ i j, MemLp (fun t => L t i j) ⊤ hardyCircleMeasure)
variable (hHerm : ∀ t, (L t).IsHermitian)
variable (m : ℝ) (hm : 0 < m)
variable (hLower : ∀ t, (L t - (m : ℂ) • 1).PosSemidef)

@[instance_reducible]
def weightedHardyCore : InnerProductSpace.Core ℂ (WeightedHardySeq r) where
  inner a b := hardyWeightedInner L (weightedUnwrap a) (weightedUnwrap b)
  conj_inner_symm a b := by
    rw [← RCLike.star_def]
    exact hardyWeightedInner_star L hHerm (weightedUnwrap b) (weightedUnwrap a)
  re_inner_nonneg a := by
    rw [RCLike.re_to_complex]
    exact (mul_nonneg hm.le (sq_nonneg ‖weightedUnwrap a‖)).trans
      (hardyWeightedInner_lower L hLp m hLower (weightedUnwrap a))
  add_left a b c := by
    rw [map_add]
    exact hardyWeightedInner_add_left L hLp _ _ _
  smul_left a b c := by
    rw [map_smul, ← RCLike.star_def]
    exact hardyWeightedInner_smul_left L c _ _
  definite a ha := by
    have h := hardyWeightedInner_lower L hLp m hLower (weightedUnwrap a)
    rw [ha, Complex.zero_re] at h
    have hsq : ‖weightedUnwrap a‖ ^ 2 = 0 := by
      nlinarith [sq_nonneg ‖weightedUnwrap a‖]
    apply weightedUnwrap.injective
    simpa only [map_zero] using norm_eq_zero.mp (sq_eq_zero_iff.mp hsq)

@[instance_reducible]
def weightedHardyNormed : NormedAddCommGroup (WeightedHardySeq r) :=
  letI : InnerProductSpace.Core ℂ (WeightedHardySeq r) :=
    weightedHardyCore L hLp hHerm m hm hLower
  InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)

@[instance_reducible]
def weightedHardyInnerProduct :
    letI : NormedAddCommGroup (WeightedHardySeq r) :=
      weightedHardyNormed L hLp hHerm m hm hLower
    InnerProductSpace ℂ (WeightedHardySeq r) :=
  letI : NormedAddCommGroup (WeightedHardySeq r) :=
    weightedHardyNormed L hLp hHerm m hm hLower
  letI : InnerProductSpace.Core ℂ (WeightedHardySeq r) :=
    weightedHardyCore L hLp hHerm m hm hLower
  InnerProductSpace.ofCore (weightedHardyCore L hLp hHerm m hm hLower).toCore

theorem weightedHardy_norm_sq (a : WeightedHardySeq r) :
    letI : NormedAddCommGroup (WeightedHardySeq r) :=
      weightedHardyNormed L hLp hHerm m hm hLower
    ‖a‖ ^ 2 = (hardyWeightedInner L (weightedUnwrap a) (weightedUnwrap a)).re := by
  letI : NormedAddCommGroup (WeightedHardySeq r) :=
    weightedHardyNormed L hLp hHerm m hm hLower
  letI : InnerProductSpace ℂ (WeightedHardySeq r) :=
    weightedHardyInnerProduct L hLp hHerm m hm hLower
  have hi : inner ℂ a a = hardyWeightedInner L (weightedUnwrap a) (weightedUnwrap a) := rfl
  simpa only [hi, RCLike.re_to_complex] using (norm_sq_eq_re_inner (𝕜 := ℂ) a)

end Yau.NodeProofs.D06Aux
