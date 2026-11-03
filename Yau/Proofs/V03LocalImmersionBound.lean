import Yau.Proofs.V03HolomorphicSmooth
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv

/-! An actual injective strict derivative on a finite-dimensional space
gives a local lower distance bound. The proof applies equally in rank zero. -/

open scoped Topology NNReal
open Filter

noncomputable section
namespace Yau.Blueprint.V03Proof

theorem local_lower_bound_of_injective_strict_derivative {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {A : E →L[ℝ] F} {p : E}
    (hf : HasStrictFDerivAt f A p) (hA : Function.Injective A) :
    ∃ r C : ℝ, 0 < r ∧ 0 ≤ C ∧ ∀ x ∈ Metric.ball p r, ∀ y ∈ Metric.ball p r,
      ‖x - y‖ ≤ C * ‖f x - f y‖ := by
  obtain ⟨K, hK, hanti⟩ := A.toLinearMap.injective_iff_antilipschitz.mp hA
  let c : ℝ≥0 := (2 * K)⁻¹
  have hc : 0 < c := by dsimp only [c]; positivity
  obtain ⟨S, hS, happ⟩ := hf.approximates_deriv_on_nhds (Or.inr hc)
  obtain ⟨r, hr, hrS⟩ := Metric.mem_nhds_iff.mp hS
  refine ⟨r, 2 * (K : ℝ), hr, by positivity, ?_⟩
  intro x hx y hy
  have herr := happ x (hrS hx) y (hrS hy)
  have hlinear : ‖x - y‖ ≤ (K : ℝ) * ‖A (x - y)‖ := by
    simpa only [dist_eq_norm, ← map_sub, ContinuousLinearMap.coe_coe] using hanti.le_mul_dist x y
  have htri : ‖A (x - y)‖ ≤ ‖f x - f y‖ + ‖f x - f y - A (x - y)‖ := by
    have hh := norm_sub_le (f x - f y) (f x - f y - A (x - y))
    have heq : f x - f y - (f x - f y - A (x - y)) = A (x - y) := by abel
    simpa only [heq] using hh
  have hKpos : (0 : ℝ) < (K : ℝ) := hK
  have hprod : (K : ℝ) * (c : ℝ) = 1 / 2 := by
    dsimp only [c]
    push_cast
    field_simp
  have hmul := mul_le_mul_of_nonneg_left (htri.trans
    (add_le_add le_rfl herr)) hKpos.le
  nlinarith [norm_nonneg (x - y), norm_nonneg (f x - f y)]

end Yau.Blueprint.V03Proof
