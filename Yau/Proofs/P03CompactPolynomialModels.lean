import Yau.Proofs.P03Polynomials
import Yau.Proofs.P03SeedDbar
import Yau.LeafProofs.L14

open scoped Manifold Topology ContDiff
open Filter Metric

noncomputable section

namespace Yau.NodeProofs.P03Aux

variable {n r : ℕ}

/-- An arbitrary finite vector of polynomial germs has one smooth compact
model representative in any prescribed neighbourhood, in every dimension. -/
theorem exists_compact_polynomial_model (c : ComplexVector n)
    (P : Fin r → MvPolynomial (Fin n) ℂ) {U : Set (ComplexVector n)} (hU : U ∈ 𝓝 c) :
    ∃ F : ComplexVector n → ComplexVector r,
      ContDiff ℝ ∞ F ∧ HasCompactSupport F ∧ tsupport F ⊆ U ∧
      F =ᶠ[𝓝 c] (fun z => WithLp.toLp 2
        (fun α => MvPolynomial.eval (fun i => z i - c i) (P α))) := by
  obtain ⟨R, hR, hRU⟩ := Metric.mem_nhds_iff.mp hU
  let b : ContDiffBump c := ⟨R / 4, R / 2, by positivity, by linarith⟩
  let Q : ComplexVector n → ComplexVector r := fun z => WithLp.toLp 2
    (fun α => MvPolynomial.eval (fun i => z i - c i) (P α))
  have hQ : ContDiff ℂ ⊤ Q :=
    (contDiff_piLp (𝕜 := ℂ) 2).mpr fun α => centeredPolynomial_contDiff (P α) c
  let F : ComplexVector n → ComplexVector r := fun z => b z • Q z
  have hsupp : tsupport F ⊆ tsupport (b : ComplexVector n → ℝ) :=
    tsupport_smul_subset_left b Q
  refine ⟨F, b.contDiff.smul ((hQ.restrict_scalars ℝ).of_le le_top),
    b.hasCompactSupport.isCompact.of_isClosed_subset (isClosed_tsupport F) hsupp, ?_, ?_⟩
  · apply hsupp.trans
    rw [b.tsupport_eq]
    intro z hz
    apply hRU
    apply Metric.mem_ball.mpr
    exact lt_of_le_of_lt (Metric.mem_closedBall.mp hz) (by dsimp [b]; linarith)
  · filter_upwards [b.eventuallyEq_one] with z hz
    change b z • Q z = Q z
    change b z = 1 at hz
    rw [hz, one_smul]

theorem polynomial_model_eventually_dbar_zero {F : ComplexVector n → ComplexVector r}
    {c : ComplexVector n} {P : Fin r → MvPolynomial (Fin n) ℂ}
    (hF : F =ᶠ[𝓝 c] (fun z => WithLp.toLp 2
      (fun α => MvPolynomial.eval (fun i => z i - c i) (P α)))) :
    Yau.LeafProofs.L14Aux.modelTopDbar F =ᶠ[𝓝 c] 0 := by
  have hd (α : Fin r) :
      fderiv ℝ (fun z => F z α) =ᶠ[𝓝 c]
        fderiv ℝ (fun z : ComplexVector n =>
          MvPolynomial.eval (fun i => z i - c i) (P α)) := by
    have he : (fun z => F z α) =ᶠ[𝓝 c] (fun z : ComplexVector n =>
        MvPolynomial.eval (fun i => z i - c i) (P α)) :=
      hF.mono fun _ hz => congrArg (fun v : ComplexVector r => v α) hz
    exact he.fderiv
  filter_upwards [Filter.eventually_all.mpr hd] with z hz
  funext i
  ext α : 1
  change wirtBar (fun w => F w α) z (stdVec i) = 0
  have he : wirtBar (fun w => F w α) z (stdVec i) =
      wirtBar (fun w : ComplexVector n => MvPolynomial.eval (fun j => w j - c j) (P α))
        z (stdVec i) := by
    simp only [wirtBar, hz α]
  rw [he]
  exact wirtBar_eq_zero_of_complex_differentiable _ z (stdVec i)
    (centeredPolynomial_differentiable (P α) c z)

end Yau.NodeProofs.P03Aux
