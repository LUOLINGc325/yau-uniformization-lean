import Yau.LeafProofs.L05PerturbationHalfUnit
import Yau.LeafProofs.L05PerturbationAffineInverse
import Yau.LeafProofs.L05PerturbationBilinearBounds

open Filter Set Metric
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

/-- The physical quarter cylinder maps into the actual unit-normalized half cylinder. -/
theorem perturb_central_twice_back {n : ℕ} {p : Point n} (hp : p ∈ backward (1/4)) :
    perturbScale 2 p ∈ backward (1/2) := by
  have hm := perturb_inverse_center_back_mem (by norm_num : (0 : ℝ) < 1/2) (0 : Point n)
    (p := p) (by convert! hp using 1 <;> norm_num [perturbBack, backward])
  simpa [perturbCenter, perturbInverseCenter, perturbScale] using hm

/-- Actual inverse affine transport, without imposing a strict buffer on the original half. -/
theorem perturb_central_actual_jets {n : ℕ} {h : Point n → ℝ}
    (hv : C2 (backward (1/2)) (fun p => h (perturbScale (1/2) p))) :
    C2 (backward (1/4)) h ∧ ∀ p ∈ backward (1/4),
      spatialD h p = (2 : ℝ) • spatialD (fun p => h (perturbScale (1/2) p)) (perturbScale 2 p) ∧
      spatialDD h p = (4 : ℝ) • spatialDD (fun p => h (perturbScale (1/2) p)) (perturbScale 2 p) ∧
      timeD (backward (1/4)) h p = (4 : ℝ) *
        timeD (backward (1/2)) (fun p => h (perturbScale (1/2) p)) (perturbScale 2 p) := by
  have hh := perturb_center_unscale_c2 (by norm_num : (0 : ℝ) < 1/2) (0 : Point n) h
    (by simpa [perturbCenter, perturbScale] using hv)
  have hc : C2 (backward (1/4)) h := by
    convert! hh.1 using 1 <;> norm_num [perturbBack, backward]
  refine ⟨hc, ?_⟩
  intro p hp
  have hp' : p ∈ perturbBack (0 : Space n) ((1/2)/2) 0 := by
    convert! hp using 1 <;> norm_num [perturbBack, backward]
  have hj := hh.2 p hp'
  refine ⟨?_, ?_, ?_⟩
  · simpa [perturbCenter, perturbInverseCenter, perturbScale] using hj.1
  · convert! hj.2.1 using 1 <;> norm_num [perturbCenter, perturbInverseCenter, perturbScale]
  · convert! hj.2.2.2 using 1 <;> norm_num [perturbCenter, perturbInverseCenter, perturbScale, perturbBack, backward]

/-- The actual scaled Holder estimate has a numerical factor at most eight. -/
theorem perturb_central_holder_transport {n : ℕ} {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] {eta C : ℝ} (heta : eta < 1)
    {f g : Point n → V} (hf : HolderBound eta (backward (1/2)) f C)
    (heq : ∀ p ∈ backward (1/4), g p = (4 : ℝ) • f (perturbScale 2 p)) :
    HolderBound eta (backward (1/4)) g (8 * C) := by
  have hpow : (2 : ℝ) ^ eta ≤ 2 := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) heta.le
  refine ⟨mul_nonneg (by norm_num) hf.1, ?_, ?_⟩
  · intro p hp
    rw [heq p hp, norm_smul]
    norm_num
    nlinarith [hf.2.1 _ (perturb_central_twice_back hp), hf.1]
  · intro p hp q hq
    rw [heq p hp, heq q hq, ← smul_sub, norm_smul]
    norm_num only [Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
    have hh := hf.2.2 _ (perturb_central_twice_back hp) _ (perturb_central_twice_back hq)
    rw [perturb_scale_weight (by norm_num : (0 : ℝ) < 2)] at hh
    have hw : 0 ≤ holderWeight eta p q := by unfold holderWeight; positivity
    have hcf : C * (2 : ℝ) ^ eta ≤ 2 * C := by nlinarith [hf.1]
    calc
      _ ≤ 4 * (C * ((2 : ℝ) ^ eta * holderWeight eta p q)) :=
        mul_le_mul_of_nonneg_left hh (by norm_num)
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hcf hw]

/-- A concrete scalar norm bound with the normed-space instance supplied explicitly. -/
theorem perturb_central_four_norm_bound {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] {v : V} {C : ℝ} (hv : ‖v‖ ≤ C) :
    ‖(4 : ℝ) • v‖ ≤ 4 * C := by
  rw [norm_smul]
  norm_num
  linarith

end Yau.LeafProofs.L05Aux
