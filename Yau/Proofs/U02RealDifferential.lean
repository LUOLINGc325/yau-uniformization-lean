import Yau.Proofs.U02MetricAlgebra

/-! Real differentiability and velocity of the same holomorphic chart map. -/

open scoped Manifold Topology ContDiff Matrix

noncomputable section
namespace Yau.NodeProofs.U02Proof
open Yau Blueprint
open Yau.LeafProofs.L12Aux

theorem contMDiffAt_real_of_complex {n m : ℕ} {M : ComplexManifold n}
    {N : ComplexManifold m} {f : M.Carrier → N.Carrier} {x : M.Carrier}
    (hf : ContMDiffAt (ComplexModel n) (ComplexModel m) ∞ f x) :
    ContMDiffAt 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ComplexVector m) ∞ f x := by
  rw [contMDiffAt_iff] at hf ⊢
  refine ⟨hf.1, ?_⟩
  convert! hf.2.restrict_scalars ℝ using 1

theorem real_derivative_in_complex_fiber {n : ℕ} {M : ComplexManifold n}
    {Phi : ComplexVector n → M.Carrier} {z : ComplexVector n}
    (hf : MDifferentiableAt 𝓘(ℂ, ComplexVector n) (ComplexModel n) Phi z)
    (v : ComplexVector n) :
    realTangentEquiv (Phi z)
      (mfderiv 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ComplexVector n) Phi z v) =
      mfderiv 𝓘(ℂ, ComplexVector n) (ComplexModel n) Phi z v := by
  let S := ComplexEuclideanManifold n (Nat.succ_le_iff.mpr (manifold_dimension_pos M))
  have hd := mfderiv_real (M := S) (N := M) hf
  have hv := congrArg (fun L => realTangentEquiv (Phi z) (L v)) hd
  change realTangentEquiv (Phi z)
      (mfderiv 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ComplexVector n) Phi z v) =
    realTangentEquiv (Phi z) ((realTangentEquiv (Phi z)).symm
      (((mfderiv 𝓘(ℂ, ComplexVector n) (ComplexModel n) Phi z).restrictScalars ℝ)
        (realTangentEquiv (M := S) z v))) at hv
  have hsource : realTangentEquiv (M := S) z v = v := rfl
  rw [ContinuousLinearEquiv.apply_symm_apply, hsource] at hv
  exact hv

theorem chart_real_contMDiffOn {n : ℕ} {M : ComplexManifold n}
    {Phi : ComplexVector n → M.Carrier} {r : ℝ}
    (hf : ContMDiffOn 𝓘(ℂ, ComplexVector n) (ComplexModel n) ∞ Phi (Metric.ball 0 r)) :
    ContMDiffOn 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ComplexVector n) ∞ Phi (Metric.ball 0 r) := by
  let S := ComplexEuclideanManifold n (Nat.succ_le_iff.mpr (manifold_dimension_pos M))
  intro z hz
  exact (contMDiffAt_real_of_complex (M := S) (N := M)
    ((hf z hz).contMDiffAt (Metric.isOpen_ball.mem_nhds hz))).contMDiffWithinAt

theorem chart_real_derivative_bound {n : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) (h : HermitianField M) (p : M.Carrier)
    (Phi : ComplexVector n → M.Carrier) {r c C ell : ℝ}
    (hc : UnitaryChart h p Phi r c C) (hC : 0 < C) (hell : 0 < ell)
    {z : ComplexVector n} (hz : z ∈ Metric.ball 0 r)
    (hmetric : HermLE (((ell ^ 2 : ℝ) : ℂ) • gMat g.form (Phi z)) (gMat h (Phi z))) :
    letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
      fun y => underlyingRealTangentNormedAddCommGroup g.form y
    ∀ v : ComplexVector n,
      ‖mfderiv 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ComplexVector n) Phi z v‖ ≤
        Real.sqrt (2 * C) / ell * ‖v‖ := by
  letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentNormedAddCommGroup g.form y
  intro v
  have hd := ((hc.1.1 z hz).contMDiffAt (Metric.isOpen_ball.mem_nhds hz)).mdifferentiableAt
    (by simp)
  have hlow := hermLE_tangent_normSq g.form h (Phi z) (ell ^ 2) hmetric
    (mfderiv 𝓘(ℂ, ComplexVector n) (ComplexModel n) Phi z v)
  have hup := unitaryChart_tangent_normSq h p Phi hc hz v
  have hsqrt := Real.sqrt_le_sqrt (show ell ^ 2 *
      (2 * hermitianNormSq (g.form (Phi z))
        (mfderiv 𝓘(ℂ, ComplexVector n) (ComplexModel n) Phi z v)) ≤
      (2 * C) * ‖v‖ ^ 2 by nlinarith)
  rw [Real.sqrt_mul (sq_nonneg ell), Real.sqrt_sq hell.le,
    Real.sqrt_mul (by positivity : 0 ≤ 2 * C), Real.sqrt_sq (norm_nonneg v)] at hsqrt
  rw [underlyingRealTangent_norm, real_derivative_in_complex_fiber hd v]
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hell).mpr
  nlinarith

end Yau.NodeProofs.U02Proof
