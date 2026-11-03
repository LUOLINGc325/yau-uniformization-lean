import Yau.Proofs.P03SpatialHessian
import Yau.LeafProofs.L22Uniform

open scoped Topology ContDiff
open Set

noncomputable section

namespace Yau.NodeProofs.P03Aux

open Yau.LeafProofs.L22Aux

theorem exists_secondFDeriv_bound_on_compact
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : E → ℝ) {O K : Set E}
    (hO : IsOpen O) (hg : ContDiffOn ℝ ∞ g O) (hK : IsCompact K) (hKO : K ⊆ O) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ K, ‖fderiv ℝ (fderiv ℝ g) p‖ ≤ C := by
  have hH : ContinuousOn (fun p => fderiv ℝ (fderiv ℝ g) p) K := by
    intro p hp
    have hgp := hg.contDiffAt (hO.mem_nhds (hKO hp))
    exact ((hgp.fderiv_right (m := ∞) (by simp)).fderiv_right
      (m := ∞) (by simp)).continuousAt.continuousWithinAt
  have hnorm : Continuous (fun T : E →L[ℝ] E →L[ℝ] ℝ => ‖T‖) := by
    exact continuous_norm (E := E →L[ℝ] E →L[ℝ] ℝ)
  have hHN := hnorm.comp_continuousOn hH
  obtain ⟨A, hA⟩ := hK.exists_bound_of_continuousOn hHN
  refine ⟨max A 0, le_max_right _ _, ?_⟩
  intro p hp
  have ha := hA p hp
  change |‖fderiv ℝ (fderiv ℝ g) p‖| ≤ A at ha
  rw [abs_of_nonneg (ContinuousLinearMap.opNorm_nonneg _)] at ha
  exact ha.trans (le_max_left _ _)

/-- One bound for the spatial Levi forms of a jointly smooth family on a
compact set of positions and parameters. The parameter is chosen after C. -/
theorem exists_uniform_spatial_levi_bound_on_compact {n : ℕ}
    (g : ComplexVector n × ℝ → ℝ) {O K : Set (ComplexVector n × ℝ)}
    (hO : IsOpen O) (hg : ContDiffOn ℝ ∞ g O) (hK : IsCompact K) (hKO : K ⊆ O) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ K, ∀ v : ComplexVector n,
      |complexLeviQuadratic (fun z => g (z, p.2)) p.1 v| ≤ C * ‖v‖ ^ 2 := by
  obtain ⟨C, hC, hHbound⟩ := exists_secondFDeriv_bound_on_compact g hO hg hK hKO
  refine ⟨C, hC, ?_⟩
  intro p hp v
  have hHp : ‖fderiv ℝ (fderiv ℝ g) p‖ ≤ C := hHbound p hp
  have hb (w : ComplexVector n) :
      |fderiv ℝ (fderiv ℝ g) p (w, 0) (w, 0)| ≤ C * ‖w‖ ^ 2 := by
    have ht := (fderiv ℝ (fderiv ℝ g) p).le_opNorm₂ (w, 0) (w, 0)
    have hn : ‖((w, 0) : ComplexVector n × ℝ)‖ = ‖w‖ := by
      simp only [Prod.norm_mk, norm_zero, max_eq_left (norm_nonneg w)]
    rw [hn, Real.norm_eq_abs] at ht
    calc
      _ ≤ ‖fderiv ℝ (fderiv ℝ g) p‖ * ‖w‖ * ‖w‖ := ht
      _ ≤ C * ‖w‖ * ‖w‖ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hHp (norm_nonneg _)) (norm_nonneg _)
      _ = C * ‖w‖ ^ 2 := by ring
  have hgp : ContDiffAt ℝ 2 g (p.1, p.2) :=
    (hg.contDiffAt (hO.mem_nhds (hKO hp))).of_le (by simp)
  unfold complexLeviQuadratic
  rw [spatial_secondFDeriv g p.1 v v p.2 hgp,
    spatial_secondFDeriv g p.1 (Complex.I • v) (Complex.I • v) p.2 hgp]
  have h1 := hb v
  have h2 := hb (Complex.I • v)
  simp only [norm_smul, Complex.norm_I, one_mul] at h2
  have hs := abs_add_le (fderiv ℝ (fderiv ℝ g) p (v, 0) (v, 0))
    (fderiv ℝ (fderiv ℝ g) p (Complex.I • v, 0) (Complex.I • v, 0))
  rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
  have hn := mul_nonneg hC (sq_nonneg ‖v‖)
  nlinarith

end Yau.NodeProofs.P03Aux
