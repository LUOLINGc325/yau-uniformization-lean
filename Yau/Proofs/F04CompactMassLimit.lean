import Yau.Proofs.F04MassCutoffLimit
import Yau.Proofs.F04MassTimeSlices

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold

noncomputable section

namespace Yau.F04Proof

open Yau.Blueprint Yau.LeafProofs.L18Aux

theorem cutoff_weight_integrable {n : ℕ} (X : KahlerManifold n) (o : Pt X)
    (u : Pt X → ℝ) (hu : ControlledExhaustion X o u)
    (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
    {f : Pt X → ℝ} (hf : Continuous f) {R : ℝ} (hR : 0 < R) :
    Integrable (fun x => massCutoff u R x * f x) μ :=
  initial_volume_integrable_of_continuous_compact X.metric μ hμ
    ((continuous_of_smoothFn (massCutoff_smooth hu.1 R)).mul hf)
    (massCutoff_compact X o u hu hR).mul_right

theorem compact_mass_monotone {n : ℕ} (X : KahlerManifold n) (o : Pt X)
    (u : Pt X → ℝ) (hu : ControlledExhaustion X o u)
    (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
    {f : Pt X → ℝ} (hf : Continuous f) (hf0 : ∀ x, 0 ≤ f x) :
    Monotone (fun N : ℕ => ∫ x, massCutoff u ((N : ℝ) + 1) x * f x ∂μ) := by
  intro N L hNL
  apply integral_mono (cutoff_weight_integrable X o u hu μ hμ hf (by positivity))
    (cutoff_weight_integrable X o u hu μ hμ hf (by positivity))
  intro x
  apply mul_le_mul_of_nonneg_right _ (hf0 x)
  apply massCutoff_mono u (fun y => le_trans zero_le_one (hu.2.2.1 y)) (by positivity)
  exact_mod_cast Nat.add_le_add_right hNL 1

/-- Vanishing of every finite compact mass forces pointwise vanishing.
No integral on the whole noncompact manifold is differentiated or assumed finite. -/
theorem compact_masses_zero_implies_zero {n : ℕ} (X : KahlerManifold n) (o : Pt X)
    (u : Pt X → ℝ) (hu : ControlledExhaustion X o u)
    (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
    {f : Pt X → ℝ} (hf : Continuous f) (hf0 : ∀ x, 0 ≤ f x)
    (hmass : ∀ N : ℕ, (∫ x, massCutoff u ((N : ℝ) + 1) x * f x ∂μ) = 0) :
    ∀ x, f x = 0 := by
  let : μ.IsOpenPosMeasure := riemannianVolume_isOpenPosMeasure X.metric μ hμ
  have heq (N : ℕ) : (fun x => massCutoff u ((N : ℝ) + 1) x * f x) = (fun _ => (0 : ℝ)) := by
    have hi := cutoff_weight_integrable X o u hu μ hμ hf (R := (N : ℝ) + 1) (by positivity)
    have hae := (integral_eq_zero_iff_of_nonneg
      (fun x => mul_nonneg (massCutoff_range u ((N : ℝ) + 1) x).1 (hf0 x)) hi).mp (hmass N)
    exact Measure.eq_of_ae_eq hae
      ((continuous_of_smoothFn (massCutoff_smooth hu.1 ((N : ℝ) + 1))).mul hf) continuous_const
  intro x
  obtain ⟨N, hN⟩ := exists_nat_gt (u x)
  have hx := congrFun (heq N) x
  rw [massCutoff_one u (show (0 : ℝ) < (N : ℝ) + 1 by positivity)
    (show u x ≤ (N : ℝ) + 1 by linarith), one_mul] at hx
  exact hx

end Yau.F04Proof
