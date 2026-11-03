import Yau.Proofs.F04RhoMass
import Yau.Proofs.F04MassCutoff

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold

noncomputable section

namespace Yau.F04Proof

open Yau.Blueprint

theorem controlled_sublevel_in_ball {n : ℕ} (X : KahlerManifold n) (o : Pt X)
    (u : Pt X → ℝ) (hu : ControlledExhaustion X o u) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ R : ℝ, 1 ≤ R →
      {x | u x ≤ 2 * R} ⊆ distBall X.metric.form o (A * R) := by
  obtain ⟨C, hC, hcontrol⟩ := hu.2.2.2
  refine ⟨max (2 * C) 1, le_max_right _ _, ?_⟩
  intro R hR x hx
  have hRp : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hAp : 0 < max (2 * C) 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  apply (LeafProofs.L12Aux.mem_distBall_iff X.metric o x (mul_pos hAp hRp)).mpr
  change distFrom X.metric.form o x < max (2 * C) 1 * R
  have hleft := mul_le_mul_of_nonneg_left (hcontrol x).1 hC.le
  rw [← mul_assoc, mul_inv_cancel₀ hC.ne', one_mul] at hleft
  have hright := mul_le_mul_of_nonneg_left hx hC.le
  have hAR := mul_le_mul_of_nonneg_right (le_max_left (2 * C) 1) hRp.le
  nlinarith

theorem flow_rho_sublevel_mass_polynomial {n : ℕ} (X : KahlerManifold n) (o : Pt X)
    (h : Flow X) (U P ρ : STF X) (hloc : LocalizedFlow X o h U P ρ)
    (u : Pt X → ℝ) (hu : ControlledExhaustion X o u)
    (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
    {T : ℝ} (hT : 0 < T) :
    ∃ D : ℝ, 0 < D ∧ ∀ R : ℝ, 1 ≤ R → ∀ t ∈ Icc 0 T,
      IntegrableOn (fun x => ρ x t) {x | u x ≤ 2 * R} μ ∧
        (∫ x in {x | u x ≤ 2 * R}, ρ x t ∂μ) ≤ D * R ^ (2 * n + 1) := by
  obtain ⟨A, hA, hsub⟩ := controlled_sublevel_in_ball X o u hu
  obtain ⟨B, hB, hball⟩ := flow_rho_ball_mass_polynomial X o h U P ρ hloc μ hμ hT
  refine ⟨B * A ^ (2 * n + 1), mul_pos hB (pow_pos (lt_of_lt_of_le zero_lt_one hA) _), ?_⟩
  intro R hR t ht
  have hAR : 1 ≤ A * R := one_le_mul_of_one_le_of_one_le hA hR
  have hb := hball (A * R) hAR t ht
  refine ⟨hb.1.mono_set (hsub R hR), ?_⟩
  calc
    _ ≤ ∫ x in distBall X.metric.form o (A * R), ρ x t ∂μ :=
      integral_mono_measure (Measure.restrict_mono_set μ (hsub R hR))
        (ae_of_all _ (fun x => rho_nonneg o h U P ρ hloc x t ht.1)) hb.1
    _ ≤ B * (A * R) ^ (2 * n + 1) := hb.2
    _ = (B * A ^ (2 * n + 1)) * R ^ (2 * n + 1) := by rw [mul_pow]; ring

end Yau.F04Proof
