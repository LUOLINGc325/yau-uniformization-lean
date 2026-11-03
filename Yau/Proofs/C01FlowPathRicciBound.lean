import Yau.Proofs.C01ConstantSpeedDistance
import Yau.Proofs.C01PathRicciContinuity
import Yau.Proofs.C01RealRicciDistanceBound

/-! The genuine Ricci integral along a constant-speed path starting
at the base point has the scalar distance-growth bound. -/

noncomputable section
open MeasureTheory
open scoped Topology ContDiff Manifold

namespace Yau.NodeProofs.C01Aux
open Yau Yau.Blueprint Yau.LeafProofs.L12Aux Yau.LeafProofs.L23Aux
variable {n : ℕ} {X : KahlerManifold n} {o : Pt X}
  {h : Flow X} {U P ρ : STF X}

theorem localizedFlow_constant_path_Ricci_bound
    (hflow : LocalizedFlow X o h U P ρ) (hjoint : JointPositivity X h)
    (T : ℝ) (hT : 0 ≤ T) :
    ∃ C : ℝ, 0 < C ∧ ∀ a : ℝ, 0 < a → a ≤ T →
      ∀ (γ : ℝ → Pt X) (d : ℝ), 0 ≤ d → γ 0 = o →
      (∀ u ∈ Set.Icc (0 : ℝ) 1,
        realTangentSpeedSq (h a) (γ u) (realCurveVelocity γ u) = d ^ 2) →
      letI := manifold_realSmooth X.manifold
      ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) 3 γ →
      (∀ u ∈ Set.Icc (0 : ℝ) 1,
        0 ≤ actualRealRicciQuadratic (h a) (γ u) (realCurveVelocity γ u) ∧
        actualRealRicciQuadratic (h a) (γ u) (realCurveVelocity γ u) ≤
          C * (1 + d ^ 2) * d ^ 2 / a) ∧
      (∫ u in Set.Icc (0 : ℝ) 1,
        actualRealRicciQuadratic (h a) (γ u) (realCurveVelocity γ u)) ≤
          C * (1 + d ^ 2) * d ^ 2 / a := by
  obtain ⟨C, hC, hb⟩ := localizedFlow_realRicci_quadratic_distance_bound hflow hjoint T hT
  refine ⟨C, hC, ?_⟩
  intro a ha haT γ d hd hγ0 hspeed
  letI := manifold_realSmooth X.manifold
  intro hγ
  have hk := localizedFlow_metricSmooth_nonneg hflow a ha.le
  have hdist := constant_speed_path_distance_le (h a) hk γ d hd hspeed (hγ.of_le (by norm_num))
  have hpoint (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
      0 ≤ actualRealRicciQuadratic (h a) (γ u) (realCurveVelocity γ u) ∧
      actualRealRicciQuadratic (h a) (γ u) (realCurveVelocity γ u) ≤
        C * (1 + d ^ 2) * d ^ 2 / a := by
    have HD : inducedDistance (h a) (γ u) o ≤ d := by
      rw [inducedDistance_symm (h a) hk, ← hγ0]
      exact hdist u hu
    have HD2 : inducedDistance (h a) (γ u) o ^ 2 ≤ d ^ 2 :=
      (sq_le_sq₀ (inducedDistance_nonneg (h a) hk _ _) hd).mpr HD
    have HR := hb a ha haT (γ u) (realCurveVelocity γ u)
    rw [hspeed u hu] at HR
    refine ⟨HR.1, HR.2.trans ?_⟩
    have H : (C * (1 + inducedDistance (h a) (γ u) o ^ 2) / a) * d ^ 2 ≤
        (C * (1 + d ^ 2) / a) * d ^ 2 := mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (add_le_add (le_rfl : (1 : ℝ) ≤ 1) HD2) hC.le) ha.le) (sq_nonneg d)
    exact H.trans_eq (by ring)
  refine ⟨hpoint, ?_⟩
  have hcont := localizedFlow_pathRicci_continuousOn hflow γ Set.univ isOpen_univ a ha hγ.contMDiffOn
  have hi : IntegrableOn (fun u => actualRealRicciQuadratic (h a) (γ u) (realCurveVelocity γ u))
      (Set.Icc (0 : ℝ) 1) volume :=
    (hcont.mono (Set.subset_univ _)).integrableOn_compact isCompact_Icc
  have hc : IntegrableOn (fun _u : ℝ => C * (1 + d ^ 2) * d ^ 2 / a)
      (Set.Icc (0 : ℝ) 1) volume := integrableOn_const (hs := by simp)
  have H := setIntegral_mono_on hi hc measurableSet_Icc (fun u hu => (hpoint u hu).2)
  simpa [integral_const, Measure.real] using H

end Yau.NodeProofs.C01Aux
