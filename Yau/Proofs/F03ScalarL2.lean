import spec.CHAIN.HeatScalarTargets

/-! Exact scalar L² and distance bridges for the supported energy graph. -/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal InnerProductSpace

namespace Yau.Proofs.F03Aux
open Yau HeatConcreteBindings

variable {n : ℕ} {M : ComplexManifold n}

theorem scalarL2_iff_memLp (μ : Measure M.Carrier) (f : M.Carrier → ℝ) :
    ScalarL2 μ f ↔ MemLp f 2 μ := by
  constructor
  · intro hf
    apply (memLp_two_iff_integrable_sq hf.1).mpr
    refine ⟨hf.1.pow 2, ?_⟩
    apply (hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun x => sq_nonneg (f x)))).mpr
    simpa only [sq_abs] using hf.2
  · intro hf
    refine ⟨hf.aestronglyMeasurable, ?_⟩
    have h := (hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun x => sq_nonneg (f x)))).mp
      hf.integrable_sq.2
    simpa only [sq_abs] using h

def scalarToLp {μ : Measure M.Carrier} {f : M.Carrier → ℝ} (hf : ScalarL2 μ f) : Lp ℝ 2 μ :=
  ((scalarL2_iff_memLp μ f).mp hf).toLp f

theorem scalarToLp_coe {μ : Measure M.Carrier} {f : M.Carrier → ℝ} (hf : ScalarL2 μ f) :
    scalarToLp hf =ᵐ[μ] f := ((scalarL2_iff_memLp μ f).mp hf).coeFn_toLp

theorem scalarL2DistanceSq_eq_norm {μ : Measure M.Carrier} {f k : M.Carrier → ℝ}
    (hf : ScalarL2 μ f) (hk : ScalarL2 μ k) :
    scalarL2DistanceSq μ f k = ENNReal.ofReal (‖scalarToLp hf - scalarToLp hk‖ ^ 2) := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  have hi := (Lp.memLp (scalarToLp hf - scalarToLp hk)).integrable_sq
  have heq : ENNReal.ofReal (∫ x, ⟪(scalarToLp hf - scalarToLp hk) x,
      (scalarToLp hf - scalarToLp hk) x⟫_ℝ ∂μ) =
      ∫⁻ x, ENNReal.ofReal (((scalarToLp hf - scalarToLp hk) x) ^ 2) ∂μ := by
    simp only [RCLike.inner_apply, conj_trivial, ← pow_two]
    exact ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ (fun x => sq_nonneg _))
  rw [heq]
  apply lintegral_congr_ae
  filter_upwards [Lp.coeFn_sub (scalarToLp hf) (scalarToLp hk),
    scalarToLp_coe hf, scalarToLp_coe hk] with x hsub hfx hkx
  simp only [hsub, Pi.sub_apply, hfx, hkx, sq_abs]

end Yau.Proofs.F03Aux
