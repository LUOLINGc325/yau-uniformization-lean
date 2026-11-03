import Yau.Proofs.C07ChartChordAlgebra

open scoped Manifold Topology ContDiff

noncomputable section

namespace Yau.Proofs.C07ChartChordAux

open Yau Set

variable {n : ℕ} {M : ComplexManifold n}

def chartEnergy (k : HermitianField M) (ψ : ComplexVector n → M.Carrier)
    (q v : ComplexVector n) : ℝ :=
  hermitianNormSq (k (ψ q)) (mfderiv 𝓘(ℂ, ComplexVector n) (ComplexModel n) ψ q v)

theorem chartEnergy_real_smul (k : HermitianField M) (ψ : ComplexVector n → M.Carrier)
    (q : ComplexVector n) (t : ℝ) (v : ComplexVector n) :
    chartEnergy k ψ q ((t : ℂ) • v) = t ^ 2 * chartEnergy k ψ q v := by
  let L : ComplexVector n →L[ℂ] TangentVector M (ψ q) :=
    (mfderiv 𝓘(ℂ, ComplexVector n) (ComplexModel n) ψ q).comp
      (NormedSpace.fromTangentSpace (𝕜 := ℂ) q).symm.toContinuousLinearMap
  change hermitianNormSq (k (ψ q)) (L ((t : ℂ) • v)) =
    t ^ 2 * hermitianNormSq (k (ψ q)) (L v)
  rw [map_smul]
  exact hermitianNormSq_real_smul (k (ψ q)) t _

/-- One positive constant controls the genuine differential at every point
of the smaller closed ball and in every tangent direction. -/
theorem exists_uniform_differential_bound_of_continuous (k : HermitianField M)
    {ψ : ComplexVector n → M.Carrier} {r R : ℝ}
    (hEnergy : ContinuousOn (fun p : ComplexVector n × ComplexVector n => chartEnergy k ψ p.1 p.2)
      (Metric.ball 0 r ×ˢ Set.univ)) (hRr : R < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ q ∈ Metric.closedBall (0 : ComplexVector n) R,
      ∀ v : ComplexVector n, chartEnergy k ψ q v ≤ C * ‖v‖ ^ 2 := by
  let K := Metric.closedBall (0 : ComplexVector n) R ×ˢ Metric.closedBall (0 : ComplexVector n) 1
  have hK : IsCompact K := (isCompact_closedBall _ _).prod (isCompact_closedBall _ _)
  have hsub : K ⊆ Metric.ball (0 : ComplexVector n) r ×ˢ Set.univ :=
    fun p hp => ⟨Metric.closedBall_subset_ball hRr hp.1, mem_univ _⟩
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn (hEnergy.mono hsub)
  let C := |B| + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hunit (q u : ComplexVector n) (hq : q ∈ Metric.closedBall 0 R)
      (hu : u ∈ Metric.closedBall 0 1) : chartEnergy k ψ q u ≤ C := by
    have hb : chartEnergy k ψ q u ≤ B := (le_abs_self _).trans
      (by simpa only [Real.norm_eq_abs] using hB (q, u) ⟨hq, hu⟩)
    exact hb.trans (by dsimp [C]; linarith [le_abs_self B])
  refine ⟨C, hC, ?_⟩
  intro q hq v
  by_cases hv : v = 0
  · subst v
    have hzero : chartEnergy k ψ q 0 = 0 := by
      simpa using chartEnergy_real_smul k ψ q (0 : ℝ) (0 : ComplexVector n)
    simpa using hzero.le
  · have hnv : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
    let u : ComplexVector n := ((‖v‖⁻¹ : ℝ) : ℂ) • v
    have huNorm : ‖u‖ = 1 := by
      simp only [u, norm_smul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg v)),
        inv_mul_cancel₀ hnv]
    have hu : u ∈ Metric.closedBall (0 : ComplexVector n) 1 := by
      rw [Metric.mem_closedBall, dist_zero_right, huNorm]
    have hscale : ((‖v‖ : ℝ) : ℂ) • u = v := by
      simp only [u, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hnv,
        Complex.ofReal_one, one_smul]
    calc
      chartEnergy k ψ q v = chartEnergy k ψ q (((‖v‖ : ℝ) : ℂ) • u) :=
        congrArg (chartEnergy k ψ q) hscale.symm
      _ = ‖v‖ ^ 2 * chartEnergy k ψ q u := chartEnergy_real_smul k ψ q ‖v‖ u
      _ ≤ ‖v‖ ^ 2 * C := mul_le_mul_of_nonneg_left (hunit q u hq hu) (sq_nonneg _)
      _ = C * ‖v‖ ^ 2 := mul_comm _ _


end Yau.Proofs.C07ChartChordAux
