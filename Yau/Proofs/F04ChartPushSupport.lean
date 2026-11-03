import Yau.Proofs.F04ChartPushSmooth

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold
noncomputable section
namespace Yau.F04Proof
open Yau.Blueprint Yau.Parabolic Yau.LeafProofs.L18Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem chartPushforwardZero_spacetime_support (c : M.Carrier)
    {O : Set (Space n)} (hOt : O ⊆ chartTarget c) {Ω : Set M.Carrier}
    (hMap : chartInv c '' O ⊆ Ω) {I : Set ℝ}
    {φ : Point n → ℝ} (hφ : Test (O ×ˢ I) φ) :
    ∃ K : Set M.Carrier, IsCompact K ∧ K ⊆ Ω ∧
      ∀ t : ℝ, tsupport (chartPushforwardZero c (fun z => φ (z, t))) ⊆ K := by
  let Kc := Prod.fst '' tsupport φ
  have hKc : IsCompact Kc := hφ.2.1.image continuous_fst
  have hKcO : Kc ⊆ O := by
    rintro z ⟨p, hp, rfl⟩
    exact (hφ.2.2 hp).1
  have hKct : Kc ⊆ chartTarget c := hKcO.trans hOt
  let K := chartInv c '' Kc
  have hK : IsCompact K := hKc.image_of_continuousOn
    ((continuousOn_extChartAt_symm (I := ComplexModel n) c).mono hKct)
  have hKΩ : K ⊆ Ω := by
    rintro y ⟨z, hz, rfl⟩
    exact hMap ⟨z, hKcO hz, rfl⟩
  have hZero (t : ℝ) (y : M.Carrier) (hyK : y ∉ K) :
      chartPushforwardZero c (fun z => φ (z, t)) y = 0 := by
    by_cases hy : y ∈ (extChartAt (ComplexModel n) c).source
    · have hp : (chartPt c y, t) ∉ tsupport φ := by
        intro hp
        apply hyK
        exact ⟨chartPt c y, ⟨(chartPt c y, t), hp, rfl⟩, (extChartAt (ComplexModel n) c).left_inv hy⟩
      simp only [chartPushforwardZero, ite_eq_left hy, image_eq_zero_of_notMem_tsupport hp]
    · simp only [chartPushforwardZero, ite_eq_right hy]
  refine ⟨K, hK, hKΩ, ?_⟩
  intro t
  apply closure_minimal ?_ hK.isClosed
  intro y hy
  by_contra hyK
  exact hy (hZero t y hyK)

theorem chartPushforwardZero_spacetime_hasDerivAt (c : M.Carrier)
    {φ : Point n → ℝ} (hφ : ContDiff ℝ ∞ φ) (t : ℝ) (y : M.Carrier) :
    HasDerivAt (fun s => chartPushforwardZero c (fun z => φ (z, s)) y)
      (chartPushforwardZero c (fun z => deriv (fun s => φ (z, s)) t) y) t := by
  by_cases hy : y ∈ (extChartAt (ComplexModel n) c).source
  · have hd := ((hφ.comp ((contDiff_const (c := chartPt c y)).prodMk contDiff_id)).differentiable (by simp) t).hasDerivAt
    simpa only [Function.comp_def, id_eq, chartPushforwardZero, ite_eq_left hy] using hd
  · simpa only [chartPushforwardZero, ite_eq_right hy] using hasDerivAt_const t (0 : ℝ)

end Yau.F04Proof
