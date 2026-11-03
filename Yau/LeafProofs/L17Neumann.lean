import Yau.LeafProofs.L17HolderSpace
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Operator.Completeness
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Topology.Algebra.InfiniteSum.Module

/-! Actual convergent Neumann series, including trivial Holder spaces. -/

noncomputable section

namespace Yau.LeafProofs.L17NeumannAux

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

def neumannSeries (E : V →L[ℝ] V) : V →L[ℝ] V := ∑' k : ℕ, (-E)^k

theorem neumann_summable {E : V →L[ℝ] V} (hE : ‖E‖ < 1) :
    Summable (fun k : ℕ => (-E)^k) :=
  summable_geometric_of_norm_lt_one (by simpa only [norm_neg] using hE)

theorem neumann_left_inverse {E : V →L[ℝ] V} (hE : ‖E‖ < 1) :
    ((ContinuousLinearMap.id ℝ V)+E).comp (neumannSeries E) = ContinuousLinearMap.id ℝ V := by
  change (1+E)*(neumannSeries E) = 1
  simpa only [neumannSeries,sub_neg_eq_add] using
    mul_neg_geom_series (-E) (by simpa only [norm_neg] using hE)

theorem neumann_right_inverse {E : V →L[ℝ] V} (hE : ‖E‖ < 1) :
    (neumannSeries E).comp ((ContinuousLinearMap.id ℝ V)+E) = ContinuousLinearMap.id ℝ V := by
  change (neumannSeries E)*(1+E) = 1
  simpa only [neumannSeries,sub_neg_eq_add] using
    geom_series_mul_neg (-E) (by simpa only [norm_neg] using hE)

omit [CompleteSpace V] in
theorem neumann_norm_le {E : V →L[ℝ] V} (hE : ‖E‖ < 1) :
    ‖neumannSeries E‖ ≤ (1-‖E‖)⁻¹ := by
  have h := tsum_geometric_le_of_norm_lt_one (-E) (by simpa only [norm_neg] using hE)
  have h1 : ‖(1 : V →L[ℝ] V)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  simp only [norm_neg] at h
  change ‖neumannSeries E‖ ≤ ‖(1 : V →L[ℝ] V)‖-1+(1-‖E‖)⁻¹ at h
  linarith

omit [CompleteSpace V] in
theorem neumann_norm_le_four_thirds {E : V →L[ℝ] V} (hE : ‖E‖ ≤ 1/4) :
    ‖neumannSeries E‖ ≤ 4/3 := by
  have hlt : ‖E‖ < 1 := by linarith
  apply (neumann_norm_le hlt).trans
  rw [inv_le_iff_one_le_mul₀ (by linarith : 0 < 1-‖E‖)]
  nlinarith

theorem neumann_apply_summable {E : V →L[ℝ] V} (hE : ‖E‖ < 1) (v : V) :
    Summable (fun k : ℕ => ((-E)^k) v) :=
  (ContinuousLinearMap.apply ℝ V v).summable (neumann_summable hE)

theorem neumann_apply {E : V →L[ℝ] V} (hE : ‖E‖ < 1) (v : V) :
    (neumannSeries E) v = ∑' k : ℕ, ((-E)^k) v :=
  (ContinuousLinearMap.apply ℝ V v).map_tsum (neumann_summable hE)

def neumannEquiv (E : V →L[ℝ] V) (hE : ‖E‖ < 1) : V ≃L[ℝ] V :=
  ContinuousLinearEquiv.equivOfInverse' ((ContinuousLinearMap.id ℝ V)+E)
    (neumannSeries E) (neumann_left_inverse hE) (neumann_right_inverse hE)

theorem neumannEquiv_apply (E : V →L[ℝ] V) (hE : ‖E‖ < 1) (v : V) :
    neumannEquiv E hE v = v+E v := rfl

theorem neumannEquiv_symm_apply (E : V →L[ℝ] V) (hE : ‖E‖ < 1) (v : V) :
    (neumannEquiv E hE).symm v = (neumannSeries E) v := rfl

open L17Aux L17HolderAux

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}
variable {P : UniformChartPartition g} {T gamma : ℝ}

theorem holderNeumann_summable_eval
    {E : HolderSpace P T gamma →L[ℝ] HolderSpace P T gamma} (hE : ‖E‖ < 1)
    (f : HolderSpace P T gamma) (q : Cylinder M T) :
    Summable (fun k : ℕ => holderFun (((-E)^k) f) q) :=
  (evalCLM P T gamma q).summable (neumann_apply_summable hE f)

theorem holderNeumann_eval
    {E : HolderSpace P T gamma →L[ℝ] HolderSpace P T gamma} (hE : ‖E‖ < 1)
    (f : HolderSpace P T gamma) (q : Cylinder M T) :
    holderFun ((neumannSeries E) f) q = ∑' k : ℕ, holderFun (((-E)^k) f) q := by
  change (evalCLM P T gamma q) ((neumannSeries E) f) = _
  rw [neumann_apply hE f]
  exact (evalCLM P T gamma q).map_tsum (neumann_apply_summable hE f)

end Yau.LeafProofs.L17NeumannAux
