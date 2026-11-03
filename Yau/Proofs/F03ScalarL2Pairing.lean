import Yau.Proofs.F03ScalarL2

/-! Exact scalar representatives and integrals of genuine L² pairings. -/

noncomputable section
open MeasureTheory Filter
open scoped InnerProductSpace

namespace Yau.Proofs.F03Aux
open Yau HeatConcreteBindings

variable {n : ℕ} {M : ComplexManifold n}

theorem scalarToLp_of_coe {μ : Measure M.Carrier} (v : Lp ℝ 2 μ)
    (hv : ScalarL2 μ (v : M.Carrier → ℝ)) : scalarToLp hv = v :=
  Lp.ext (scalarToLp_coe hv)

theorem scalarL2_product_integrable {μ : Measure M.Carrier} {f k : M.Carrier → ℝ}
    (hf : ScalarL2 μ f) (hk : ScalarL2 μ k) : Integrable (fun x => f x * k x) μ :=
  ((scalarL2_iff_memLp μ f).mp hf).integrable_mul ((scalarL2_iff_memLp μ k).mp hk)

theorem scalarToLp_inner {μ : Measure M.Carrier} {f k : M.Carrier → ℝ}
    (hf : ScalarL2 μ f) (hk : ScalarL2 μ k) :
    ⟪scalarToLp hf, scalarToLp hk⟫_ℝ = ∫ x, f x * k x ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [scalarToLp_coe hf, scalarToLp_coe hk] with x hfx hkx
  simp only [RCLike.inner_apply, conj_trivial, hfx, hkx, mul_comm]

end Yau.Proofs.F03Aux
