import Yau.Proofs.C01ScalarMonotonicity
import Yau.Proofs.C01ScalarTimeBoundary

/-! The original linear growth bound for rho and monotonicity of tR
bound the scalar curvature at each fixed point for all nonnegative times. -/

noncomputable section

open scoped Manifold Topology ContDiff Matrix ComplexOrder

namespace Yau.NodeProofs.C01Aux

open Yau Yau.Blueprint

variable {n : ℕ} {X : KahlerManifold n} {o : Pt X}
  {h : Flow X} {U P ρ : STF X}

theorem localizedFlow_scalar_large_time_bound
    (hflow : LocalizedFlow X o h U P ρ) (hjoint : JointPositivity X h) (x : Pt X) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t, 1 ≤ t → scalarCurvature (h t) x ≤ C := by
  have hmono := localizedFlow_scalar_clock_monotoneOn hflow hjoint x
  have hPtime := localizedFlow_P_time_contDiffOn hflow x
  have hcopy := hflow
  obtain ⟨_, _, _, _, _, _, _, _, _, hrho, hdP, _, hlinear, _⟩ := hcopy
  obtain ⟨A, hA⟩ := hlinear x
  let C := max A 0
  have hC : 0 ≤ C := le_max_right _ _
  have hAbound (t : ℝ) (ht : 0 ≤ t) : ρ x t ≤ C * (1 + t) :=
    (hA t ht).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith))
  refine ⟨6 * C, mul_nonneg (by norm_num) hC, ?_⟩
  intro t ht
  have htpos : 0 < t := by linarith
  have httw : t ≤ 2 * t := by linarith
  have hsub : Set.Icc t (2 * t) ⊆ Set.Ici (0 : ℝ) := by
    intro u hu
    exact htpos.le.trans hu.1
  have hhalf (u : ℝ) (hu : u ∈ Set.Icc t (2 * t)) :
      scalarCurvature (h t) x / 2 ≤ scalarCurvature (h u) x := by
    have hupos : 0 < u := htpos.trans_le hu.1
    have hm := hmono htpos hupos hu.1
    have hRu := (hdP x u hupos.le).2
    have huR := mul_le_mul_of_nonneg_right hu.2 hRu
    have hscaled : t * scalarCurvature (h t) x ≤ t * (2 * scalarCurvature (h u) x) := by
      nlinarith
    have hunscaled := le_of_mul_le_mul_left hscaled htpos
    linarith
  have hdiff : DifferentiableOn ℝ (P x) (interior (Set.Icc t (2 * t))) := by
    intro u hu
    have hupos : 0 < u := htpos.trans_le (interior_subset hu).1
    exact ((hdP x u hupos.le).1.hasDerivAt (Ici_mem_nhds hupos)).differentiableAt.differentiableWithinAt
  have hderle : ∀ u ∈ interior (Set.Icc t (2 * t)),
      deriv (P x) u ≤ -scalarCurvature (h t) x / 2 := by
    intro u hu
    have hupos : 0 < u := htpos.trans_le (interior_subset hu).1
    rw [((hdP x u hupos.le).1.hasDerivAt (Ici_mem_nhds hupos)).deriv]
    linarith [hhalf u (interior_subset hu)]
  have hmvt := (convex_Icc t (2 * t)).image_sub_le_mul_sub_of_deriv_le
    (hPtime.continuousOn.mono hsub) hdiff hderle
    t ⟨le_rfl, httw⟩ (2 * t) ⟨httw, le_rfl⟩ httw
  have hρt := hrho x t htpos.le
  have hρtw := hrho x (2 * t) (by positivity)
  have hbound := hAbound (2 * t) (by positivity)
  have hcoef : C * (1 + 2 * t) ≤ C * (3 * t) :=
    mul_le_mul_of_nonneg_left (by linarith) hC
  have hfinal : t * scalarCurvature (h t) x ≤ t * (6 * C) := by
    nlinarith [hρt.1, hρt.2, hρtw.1, hbound, hcoef, hmvt]
  exact le_of_mul_le_mul_left hfinal htpos

theorem localizedFlow_scalar_pointwise_bounded
    (hflow : LocalizedFlow X o h U P ρ) (hjoint : JointPositivity X h) (x : Pt X) :
    ∃ C : ℝ, ∀ t, 0 ≤ t → scalarCurvature (h t) x ≤ C := by
  have hsub : Set.Icc (0 : ℝ) 1 ⊆ Set.Ici 0 := by
    intro t ht
    exact ht.1
  have hcontinuous := (localizedFlow_scalar_time_contDiffOn_nonneg hflow x).continuousOn.mono hsub
  obtain ⟨B, hB⟩ := isCompact_Icc.bddAbove_image hcontinuous
  obtain ⟨C, _, hC⟩ := localizedFlow_scalar_large_time_bound hflow hjoint x
  refine ⟨max B C, ?_⟩
  intro t ht
  by_cases hsmall : t ≤ 1
  · exact (hB ⟨t, ⟨ht, hsmall⟩, rfl⟩).trans (le_max_left _ _)
  · exact (hC t (le_of_not_ge hsmall)).trans (le_max_right _ _)

theorem localizedFlow_basepoint_scalar_bound
    (hflow : LocalizedFlow X o h U P ρ) (hjoint : JointPositivity X h) :
    ∃ C : ℝ, ∀ t, 0 ≤ t → scalarCurvature (h t) o ≤ C :=
  localizedFlow_scalar_pointwise_bounded hflow hjoint o

end Yau.NodeProofs.C01Aux
