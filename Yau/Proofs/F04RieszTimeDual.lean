import Yau.Proofs.F04TimeBilinear
import Yau.Proofs.F04SameTraceEnergy
import Yau.Proofs.F04DualPairing

open MeasureTheory Filter
open scoped Topology InnerProductSpace ENNReal

noncomputable section

namespace Yau.F04Proof

open Yau.LeafProofs.L16LionsTimeTrace

variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

omit [CompleteSpace V] [CompleteSpace H] in
theorem hilbertPivot_norm_le_one (j : V →L[ℝ] H) (hj : ‖j‖ ≤ 1) :
    ‖hilbertPivot j‖ ≤ 1 := by
  apply (hilbertPivot j).opNorm_le_bound₂ zero_le_one
  intro u v
  have hv : ‖j v‖ ≤ ‖v‖ := by
    simpa only [one_mul] using (j.le_opNorm v).trans (mul_le_mul_of_nonneg_right hj (norm_nonneg _))
  change ‖inner ℝ u (j v)‖ ≤ 1 * ‖u‖ * ‖v‖
  simpa only [one_mul] using (norm_inner_le_norm u (j v)).trans
    (mul_le_mul_of_nonneg_left hv (norm_nonneg _))

/-- Riesz in the genuine time Hilbert space constructs an actual L2 energy
 dual residual. No pointwise strong-measurability oracle for B(t)U(t) is used. -/
theorem time_dual_residual_exists
    (j : V →L[ℝ] H) (hj : ‖j‖ ≤ 1)
    (B : ℝ → V →L[ℝ] V →L[ℝ] ℝ) (C : ℝ) (hC : 0 ≤ C) (hB : ∀ t, ‖B t‖ ≤ C)
    (hc : ∀ u v, Continuous (fun t => B t u v)) (ν : Measure ℝ)
    (f : Lp H 2 ν) (U : Lp V 2 ν) :
    ∃ R : ℝ → StrongDual ℝ V,
      MemLp R 2 ν ∧
      (∫ t, ‖R t‖ ^ 2 ∂ν) ≤ (‖f‖ + C * ‖U‖) ^ 2 ∧
      ∀ W : Lp V 2 ν,
        (∫ t, R t (W t) ∂ν) =
          (∫ t, inner ℝ (f t) (j (W t)) ∂ν) - ∫ t, B t (U t) (W t) ∂ν := by
  let Fop := variationalTimeBilinear (fun _ => hilbertPivot j) 1 zero_le_one
    (fun _ => hilbertPivot_norm_le_one j hj) (fun _ _ => continuous_const) ν
  let Bop := variationalTimeBilinear B C hC hB hc ν
  let L : StrongDual ℝ (Lp V 2 ν) := Fop f - Bop U
  have hFnorm : ‖Fop f‖ ≤ ‖f‖ := by
    simpa only [one_mul] using variationalTimeBilinear_section_norm_le
      (fun _ => hilbertPivot j) 1 zero_le_one (fun _ => hilbertPivot_norm_le_one j hj)
      (fun _ _ => continuous_const) ν f
  have hBnorm : ‖Bop U‖ ≤ C * ‖U‖ := variationalTimeBilinear_section_norm_le B C hC hB hc ν U
  have hLnorm : ‖L‖ ≤ ‖f‖ + C * ‖U‖ := by
    apply L.opNorm_le_bound (add_nonneg (norm_nonneg _) (mul_nonneg hC (norm_nonneg _)))
    intro W
    change ‖Fop f W - Bop U W‖ ≤ _
    calc
      _ ≤ ‖Fop f W‖ + ‖Bop U W‖ := norm_sub_le _ _
      _ ≤ ‖Fop f‖ * ‖W‖ + ‖Bop U‖ * ‖W‖ :=
        add_le_add ((Fop f).le_opNorm W) ((Bop U).le_opNorm W)
      _ ≤ ‖f‖ * ‖W‖ + (C * ‖U‖) * ‖W‖ :=
        add_le_add (mul_le_mul_of_nonneg_right hFnorm (norm_nonneg W))
          (mul_le_mul_of_nonneg_right hBnorm (norm_nonneg W))
      _ = _ := by ring
  let q := (InnerProductSpace.toDual ℝ (Lp V 2 ν)).symm L
  let Jd : V →L[ℝ] StrongDual ℝ V :=
    (InnerProductSpace.toDual ℝ V).toContinuousLinearEquiv.toContinuousLinearMap
  let R := fun t => Jd (q t)
  have hR : MemLp R 2 ν := (Lp.memLp q).continuousLinearMap_comp Jd
  have hqnorm : ‖q‖ = ‖L‖ := (InnerProductSpace.toDual ℝ (Lp V 2 ν)).symm.norm_map L
  have hRnorm : (∫ t, ‖R t‖ ^ 2 ∂ν) = ‖q‖ ^ 2 := by
    rw [bochner_l2_norm_sq_integral q]
    apply integral_congr_ae
    apply ae_of_all
    intro t
    change ‖(InnerProductSpace.toDual ℝ V) (q t)‖ ^ 2 = ‖q t‖ ^ 2
    rw [LinearIsometryEquiv.norm_map]
  refine ⟨R, hR, ?_, ?_⟩
  · rw [hRnorm, hqnorm]
    exact (sq_le_sq₀ (norm_nonneg L) (add_nonneg (norm_nonneg _) (mul_nonneg hC (norm_nonneg _)))).mpr hLnorm
  · intro W
    have hqL : inner ℝ q W = L W := by
      dsimp only [q]
      rw [InnerProductSpace.toDual_symm_apply]
    calc
      (∫ t, R t (W t) ∂ν) = inner ℝ q W := by
        rw [L2.inner_def]
        apply integral_congr_ae
        exact ae_of_all _ (fun _ => rfl)
      _ = L W := hqL
      _ = _ := by
        dsimp only [L, Fop, Bop]
        simp only [sub_apply, variationalTimeBilinear_apply, hilbertPivot_apply]

end Yau.F04Proof
