import Yau.Proofs.G01BisectionalNumerator

/-! The original paper-positive hypothesis yields nonnegative native
Chern bisectional curvature, using the genuinely consumed normalization API. -/
noncomputable section
open scoped Manifold
namespace Yau.NodeProofs.F01Aux
open Yau
variable {n : ℕ} {M : ComplexManifold n}

theorem nonnegBisectional_of_paperPositive (g : SmoothMetric M)
    (hp : PaperPositiveBisectional g.form) : NonnegBisectional g.form := by
  intro x ξ η
  by_cases hξ : ξ = 0
  · subst ξ
    simp [bisectionalForm]
  by_cases hη : η = 0
  · subst η
    simp [bisectionalForm]
  let u := chartVec x x ξ
  let v := chartVec x x η
  have hcξ : tangentCoordinates x u = ξ :=
    Yau.LeafProofs.L12Aux.tangentCoords_chartVec x x (mem_extChartAt_source x) ξ
  have hcη : tangentCoordinates x v = η :=
    Yau.LeafProofs.L12Aux.tangentCoords_chartVec x x (mem_extChartAt_source x) η
  have hu : u ≠ 0 := by
    intro hu0
    have hh := hcξ
    rw [hu0] at hh
    have hzero : tangentCoordinates x (0 : TangentVector M x) = 0 := by
      change tangentCoords x x 0 = 0
      exact map_zero _
    rw [hzero] at hh
    exact hξ hh.symm
  have hv : v ≠ 0 := by
    intro hv0
    have hh := hcη
    rw [hv0] at hh
    have hzero : tangentCoordinates x (0 : TangentVector M x) = 0 := by
      change tangentCoords x x 0 = 0
      exact map_zero _
    rw [hzero] at hh
    exact hη hh.symm
  have hh := hp x u v hu hv
  change 0 < paperBisectionalNumerator g.form x u v at hh
  rw [Yau.NodeProofs.G01Aux.paper_numerator_eq_bisectionalForm g.form
    (Yau.LeafProofs.L12Aux.metricSmooth_of_smoothMetric g) g.kahler_equations,
    hcξ, hcη] at hh
  linarith

theorem kahlerManifold_nonnegBisectional (X : KahlerManifold n) :
    NonnegBisectional X.metric.form :=
  nonnegBisectional_of_paperPositive X.metric X.positive_bisectional_curvature

end Yau.NodeProofs.F01Aux
