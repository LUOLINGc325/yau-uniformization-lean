import Yau.LeafProofs.L22LeviCalculus

noncomputable section

open scoped Topology ContDiff Manifold Matrix ComplexOrder
open Filter

namespace Yau.LeafProofs.L22Aux

/-- Positive Levi forms pull back along holomorphic maps with injective differential. -/
theorem leviC_posDef_comp {n m : ℕ}
    {T : ComplexVector n → ComplexVector m} {f : ComplexVector m → ℝ}
    {z : ComplexVector n} (hT : ContDiffAt ℂ 2 T z)
    (hf : ContDiffAt ℝ 2 f (T z)) (hinj : Function.Injective (fderiv ℂ T z))
    (hpos : (leviC f (T z)).PosDef) : (leviC (f ∘ T) z).PosDef := by
  apply (leviC_posDef_iff (hf.comp z (hT.restrict_scalars ℝ))).2
  intro v hv
  rw [complexLeviQuadratic_comp hT hf]
  apply (leviC_posDef_iff hf).1 hpos
  exact fun hz => hv (hinj (by simpa using hz))

/-- The true chart-transition differential is injective, by the two inverse frame maps. -/
theorem chartTransition_fderiv_injective {n : ℕ} {M : ComplexManifold n}
    (a b : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget a)
    (hy : chartInv a z ∈ (extChartAt (ComplexModel n) b).source) :
    Function.Injective (fderiv ℂ (fun w => chartPt b (chartInv a w)) z) := by
  have ha : chartInv a z ∈ (extChartAt (ComplexModel n) a).source :=
    (extChartAt (ComplexModel n) a).map_target hz
  intro v w hvw
  rw [L18Aux.chartTransition_fderiv a b hz hy,
    L18Aux.chartTransition_fderiv a b hz hy] at hvw
  have h := congrArg (fun q => chartVec b (chartInv a z) q) hvw
  rw [L12Aux.chartVec_tangentCoords b _ hy,
    L12Aux.chartVec_tangentCoords b _ hy] at h
  have h' := congrArg (fun q => tangentCoords a (chartInv a z) q) h
  simpa only [L12Aux.tangentCoords_chartVec a _ ha] using h'

/-- Pointwise strict Levi positivity is preserved by an actual overlapping chart change. -/
theorem leviC_posDef_chart_comp {n : ℕ} {M : ComplexManifold n}
    (a b : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget a)
    (hy : chartInv a z ∈ (extChartAt (ComplexModel n) b).source)
    {f : ComplexVector n → ℝ} (hf : ContDiffAt ℝ 2 f (chartPt b (chartInv a z)))
    (hpos : (leviC f (chartPt b (chartInv a z))).PosDef) :
    (leviC (f ∘ fun w => chartPt b (chartInv a w)) z).PosDef := by
  apply leviC_posDef_comp ((L18Aux.chartTransition_contDiffAt a b hz hy).of_le (by simp)) hf
    (chartTransition_fderiv_injective a b hz hy) hpos

/-- A smooth strictly positive branch in chart `a` has positive Levi at every point of its domain. -/
theorem levi_posDef_chart_branch {n : ℕ} {M : ComplexManifold n}
    (a x : M.Carrier) (hx : x ∈ (extChartAt (ComplexModel n) a).source)
    {h : ComplexVector n → ℝ} (hh : ContDiffAt ℝ 2 h (chartPt a x))
    (hpos : (leviC h (chartPt a x)).PosDef) :
    (levi (fun y => h (chartPt a y)) x).PosDef := by
  have hi : chartInv x (chartPt x x) = x :=
    (extChartAt (ComplexModel n) x).left_inv (mem_extChartAt_source x)
  have hx' : chartInv x (chartPt x x) ∈ (extChartAt (ComplexModel n) a).source := by
    simpa only [hi] using hx
  have hh' : ContDiffAt ℝ 2 h (chartPt a (chartInv x (chartPt x x))) := by
    simpa only [hi] using hh
  have hpos' : (leviC h (chartPt a (chartInv x (chartPt x x)))).PosDef := by
    simpa only [hi] using hpos
  exact leviC_posDef_chart_comp x a (mem_extChartAt_target x) hx' hh' hpos'

end Yau.LeafProofs.L22Aux
