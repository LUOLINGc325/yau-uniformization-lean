import Yau.Proofs.V03CompactChartNeighborhood
import Yau.Proofs.V03CompactAmbientGraph
import Yau.Proofs.V03ImmersionChartBound
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-! Genuine chart-smooth coefficients on an intrinsic compact set have
uniform bounds and are Lipschitz in the original immersion distance. -/

open scoped Topology ContDiff Manifold

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

variable {n q : ℕ} {M : ComplexManifold n}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem cotangentCoefficient_local_lipschitz
    {G : CotangentPoint M → ComplexVector q} (hG : CotangentImmersion G)
    {b : CotangentPoint M → F}
    (hb : ∀ x : M.Carrier, ContDiffOn ℝ ∞ (fun z => b (cotangentChartInv x z)) (cotangentTarget x))
    (x : M.Carrier) {z : CotangentCoord n} (hz : z ∈ cotangentTarget x) :
    ∃ r C : ℝ, 0 < r ∧ 0 ≤ C ∧ Metric.ball z r ⊆ cotangentTarget x ∧
      ∀ u ∈ Metric.ball z r, ∀ v ∈ Metric.ball z r,
      ‖b (cotangentChartInv x u) - b (cotangentChartInv x v)‖ ≤
        C * ‖G (cotangentChartInv x u) - G (cotangentChartInv x v)‖ := by
  obtain ⟨r, C₀, hr, hC₀, hrS, hlow⟩ := cotangentImmersion_local_chart_bound hG x hz
  have hball : Metric.closedBall z (r / 2) ⊆ Metric.ball z r :=
    Metric.closedBall_subset_ball (half_lt_self hr)
  obtain ⟨K, hK⟩ := ((hb x).mono (hball.trans hrS)).exists_lipschitzOnWith (by simp)
    (convex_closedBall z (r / 2)) (isCompact_closedBall z (r / 2))
  refine ⟨r / 2, (K : ℝ) * C₀, half_pos hr, mul_nonneg K.2 hC₀,
    (Metric.ball_subset_ball (half_le_self hr.le)).trans hrS, ?_⟩
  intro u hu v hv
  have hu' := Metric.ball_subset_closedBall hu
  have hv' := Metric.ball_subset_closedBall hv
  have hh := hK.dist_le_mul u hu' v hv'
  rw [dist_eq_norm, dist_eq_norm] at hh
  have hh₂ : (K : ℝ) * ‖u - v‖ ≤ (K : ℝ) *
      (C₀ * ‖G (cotangentChartInv x u) - G (cotangentChartInv x v)‖) := by
    gcongr
    exact hlow u (hball hu') v (hball hv')
  exact hh.trans (by simpa only [mul_assoc] using hh₂)

def compactImmersionCoefficient (G : CotangentPoint M → ComplexVector q)
    (b : CotangentPoint M → F) (K : Set (CotangentPoint M)) (p : G '' K) : F :=
  b (compactImmersionPoint G p)

theorem compactImmersionCoefficient_locallyLipschitz
    {G : CotangentPoint M → ComplexVector q} (hG : CotangentImmersion G)
    {b : CotangentPoint M → F}
    (hb : ∀ x : M.Carrier, ContDiffOn ℝ ∞ (fun z => b (cotangentChartInv x z)) (cotangentTarget x))
    {K : Set (CotangentPoint M)} (hK : CotangentCompact K) :
    LocallyLipschitz (compactImmersionCoefficient G b K) := by
  intro p
  let y := compactImmersionPoint G p
  have hyK : y ∈ K := compactImmersionPoint_mem G p
  have hy : y ∈ cotangentSource y.1 := mem_extChartAt_source _
  obtain ⟨r, C, hr, hC, _, hbound⟩ := cotangentCoefficient_local_lipschitz hG hb y.1
    (cotangentChart_mapsTo y.1 hy)
  obtain ⟨δ, hδ, hnear⟩ := compact_cotangent_chart_neighborhood hG hK hyK y.1 hy hr
  let c : NNReal := ⟨C, hC⟩
  refine ⟨c, Metric.ball p δ, Metric.ball_mem_nhds p hδ, ?_⟩
  apply LipschitzOnWith.of_dist_le_mul
  intro p₁ hp₁ p₂ hp₂
  have hchart (p' : G '' K) (hp' : p' ∈ Metric.ball p δ) :
      compactImmersionPoint G p' ∈ cotangentSource y.1 ∧
      cotangentChart y.1 (compactImmersionPoint G p') ∈ Metric.ball (cotangentChart y.1 y) r := by
    apply hnear _ (compactImmersionPoint_mem G p')
    change ‖G (compactImmersionPoint G p') - G (compactImmersionPoint G p)‖ < δ
    rw [compactImmersionPoint_image G p', compactImmersionPoint_image G p]
    simpa only [Metric.mem_ball, Subtype.dist_eq, dist_eq_norm] using hp'
  have hc₁ := hchart p₁ hp₁
  have hc₂ := hchart p₂ hp₂
  have hh := hbound _ hc₁.2 _ hc₂.2
  rw [cotangentChart_left_inv y.1 hc₁.1, cotangentChart_left_inv y.1 hc₂.1,
    compactImmersionPoint_image G p₁, compactImmersionPoint_image G p₂] at hh
  rw [dist_eq_norm]
  change ‖b (compactImmersionPoint G p₁) - b (compactImmersionPoint G p₂)‖ ≤ C * dist p₁ p₂
  simpa only [Subtype.dist_eq, dist_eq_norm] using hh

theorem cotangentCoefficient_compact_control
    {G : CotangentPoint M → ComplexVector q} (hG : CotangentImmersion G)
    {b : CotangentPoint M → F}
    (hb : ∀ x : M.Carrier, ContDiffOn ℝ ∞ (fun z => b (cotangentChartInv x z)) (cotangentTarget x))
    {K : Set (CotangentPoint M)} (hK : CotangentCompact K) :
    ∃ C B : ℝ, 0 ≤ C ∧ 0 ≤ B ∧ (∀ y ∈ K, ‖b y‖ ≤ B) ∧
      ∀ y ∈ K, ∀ y' ∈ K, ‖b y - b y'‖ ≤ C * ‖G y - G y'‖ := by
  letI : CompactSpace (G '' K) := isCompact_iff_compactSpace.mp
    (cotangentCompact_ambient_isCompact hG.1 hK)
  have hloc := compactImmersionCoefficient_locallyLipschitz hG hb hK
  obtain ⟨C, hC⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact
    (isCompact_univ : IsCompact (Set.univ : Set (G '' K))) hloc.locallyLipschitzOn
  obtain ⟨B, hB⟩ := ((isCompact_univ : IsCompact (Set.univ : Set (G '' K))).image
    hloc.continuous).isBounded.exists_norm_le
  have hpoint (y : CotangentPoint M) (hy : y ∈ K) :
      compactImmersionCoefficient G b K ⟨G y, ⟨y, hy, rfl⟩⟩ = b y := by
    unfold compactImmersionCoefficient
    rw [compactImmersionPoint_eq hG.2.1 y hy]
  refine ⟨C, max B 0, C.2, le_max_right _ _, ?_, ?_⟩
  · intro y hy
    exact (hB _ ⟨⟨G y, ⟨y, hy, rfl⟩⟩, Set.mem_univ _, hpoint y hy⟩).trans (le_max_left _ _)
  intro y hy y' hy'
  have hh := hC.dist_le_mul (⟨G y, ⟨y, hy, rfl⟩⟩ : G '' K) (Set.mem_univ _)
    ⟨G y', ⟨y', hy', rfl⟩⟩ (Set.mem_univ _)
  rw [hpoint y hy, hpoint y' hy', dist_eq_norm] at hh
  simpa only [Subtype.dist_eq, dist_eq_norm] using hh

end Yau.Blueprint.V03Proof
