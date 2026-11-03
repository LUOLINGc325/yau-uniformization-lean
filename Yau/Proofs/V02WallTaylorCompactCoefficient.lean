import Yau.Proofs.V03CompactImmersionCoefficient

/-! Locally chart-smooth coefficients, with compact auxiliary real parameters,
are uniformly bounded and Lipschitz in the actual immersion distance. -/

open scoped Topology ContDiff Manifold

noncomputable section
namespace Yau.Blueprint.V02WallTaylorProof
open Yau Yau.Blueprint V03Proof

variable {n q : ℕ} {M : ComplexManifold n}
  {P F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def compactAugmentedCoefficient (G : CotangentPoint M → ComplexVector q)
    (b : CotangentPoint M → P → F) (K : Set (CotangentPoint M)) (L : Set P)
    (p : (G '' K) × L) : F := b (compactImmersionPoint G p.1) p.2

theorem compactAugmentedCoefficient_locallyLipschitz
    {G : CotangentPoint M → ComplexVector q} (hG : CotangentImmersion G)
    {b : CotangentPoint M → P → F} {K : Set (CotangentPoint M)} (hK : CotangentCompact K)
    {L : Set P}
    (hb : ∀ y ∈ K, ∀ p ∈ L,
      ContDiffAt ℝ 1 (fun w : CotangentCoord n × P => b (cotangentChartInv y.1 w.1) w.2)
        (cotangentChart y.1 y, p)) :
    LocallyLipschitz (compactAugmentedCoefficient G b K L) := by
  intro p
  have hfst (s t : (G '' K) × L) : dist s.1 t.1 ≤ dist s t := by
    rw [Prod.dist_eq]; exact le_max_left _ _
  have hsnd (s t : (G '' K) × L) : dist s.2 t.2 ≤ dist s t := by
    rw [Prod.dist_eq]; exact le_max_right _ _
  let y := compactImmersionPoint G p.1
  have hyK : y ∈ K := compactImmersionPoint_mem G p.1
  have hy : y ∈ cotangentSource y.1 := mem_extChartAt_source _
  obtain ⟨A, V, hV, hLip⟩ := (hb y hyK p.2 p.2.2).exists_lipschitzOnWith
  obtain ⟨ε, hε, hεV⟩ := Metric.mem_nhds_iff.mp hV
  obtain ⟨r, C, hr, hC, _, hlow⟩ :=
    cotangentImmersion_local_chart_bound hG y.1 (cotangentChart_mapsTo y.1 hy)
  obtain ⟨η, hη, hnear⟩ := compact_cotangent_chart_neighborhood hG hK hyK y.1 hy
    (lt_min hr hε)
  let B : NNReal := ⟨(A : ℝ) * (C + 1), mul_nonneg A.2 (by linarith)⟩
  refine ⟨B, Metric.ball p (min η ε), Metric.ball_mem_nhds p (lt_min hη hε), ?_⟩
  apply LipschitzOnWith.of_dist_le_mul
  intro p₁ hp₁ p₂ hp₂
  have hchart (p' : (G '' K) × L) (hp' : p' ∈ Metric.ball p (min η ε)) :
      compactImmersionPoint G p'.1 ∈ cotangentSource y.1 ∧
      cotangentChart y.1 (compactImmersionPoint G p'.1) ∈
        Metric.ball (cotangentChart y.1 y) (min r ε) := by
    apply hnear _ (compactImmersionPoint_mem G _)
    rw [compactImmersionPoint_image G p'.1, compactImmersionPoint_image G p.1]
    exact (show ‖p'.1.1 - p.1.1‖ ≤ dist p' p from by
      simpa only [Subtype.dist_eq, dist_eq_norm] using (hfst p' p)).trans_lt
        (lt_of_lt_of_le hp' (min_le_left η ε))
  have hc₁ := hchart p₁ hp₁
  have hc₂ := hchart p₂ hp₂
  have hmem (p' : (G '' K) × L) (hp' : p' ∈ Metric.ball p (min η ε)) :
      (cotangentChart y.1 (compactImmersionPoint G p'.1), (p'.2 : P)) ∈ V := by
    apply hεV
    rw [Metric.mem_ball, Prod.dist_eq]
    apply max_lt
    · exact lt_of_lt_of_le (hchart p' hp').2 (min_le_right r ε)
    · exact (hsnd p' p).trans_lt (lt_of_lt_of_le hp' (min_le_right η ε))
  have hh := hLip.dist_le_mul _ (hmem p₁ hp₁) _ (hmem p₂ hp₂)
  have hlow' := hlow _ (Metric.ball_subset_ball (min_le_left r ε) hc₁.2)
    _ (Metric.ball_subset_ball (min_le_left r ε) hc₂.2)
  rw [cotangentChart_left_inv y.1 hc₁.1, cotangentChart_left_inv y.1 hc₂.1,
    compactImmersionPoint_image G p₁.1, compactImmersionPoint_image G p₂.1] at hlow'
  rw [cotangentChart_left_inv y.1 hc₁.1, cotangentChart_left_inv y.1 hc₂.1] at hh
  have hcoord : ‖cotangentChart y.1 (compactImmersionPoint G p₁.1) -
      cotangentChart y.1 (compactImmersionPoint G p₂.1)‖ ≤ C * dist p₁ p₂ :=
    hlow'.trans (mul_le_mul_of_nonneg_left (by
      simpa only [Subtype.dist_eq, dist_eq_norm] using hfst p₁ p₂) hC)
  have haux : ‖(p₁.2 : P) - p₂.2‖ ≤ dist p₁ p₂ := by
    simpa only [Subtype.dist_eq, dist_eq_norm] using hsnd p₁ p₂
  have hdist : dist (cotangentChart y.1 (compactImmersionPoint G p₁.1), (p₁.2 : P))
      (cotangentChart y.1 (compactImmersionPoint G p₂.1), (p₂.2 : P)) ≤
        (C + 1) * dist p₁ p₂ := by
    rw [Prod.dist_eq, dist_eq_norm, dist_eq_norm]
    exact max_le (hcoord.trans (by nlinarith [dist_nonneg (x := p₁) (y := p₂)]))
      (haux.trans (by nlinarith [dist_nonneg (x := p₁) (y := p₂)]))
  exact hh.trans ((mul_le_mul_of_nonneg_left hdist A.2).trans_eq (by
    change (A : ℝ) * ((C + 1) * dist p₁ p₂) = _
    change (A : ℝ) * ((C + 1) * dist p₁ p₂) = (A : ℝ) * (C + 1) * dist p₁ p₂
    ring))

theorem augmentedCoefficient_compact_control
    {G : CotangentPoint M → ComplexVector q} (hG : CotangentImmersion G)
    {b : CotangentPoint M → P → F} {K : Set (CotangentPoint M)} (hK : CotangentCompact K)
    {L : Set P} (hL : IsCompact L)
    (hb : ∀ y ∈ K, ∀ p ∈ L,
      ContDiffAt ℝ 1 (fun w : CotangentCoord n × P => b (cotangentChartInv y.1 w.1) w.2)
        (cotangentChart y.1 y, p)) :
    ∃ C B : ℝ, 0 ≤ C ∧ 0 ≤ B ∧ (∀ y ∈ K, ∀ p ∈ L, ‖b y p‖ ≤ B) ∧
      ∀ y ∈ K, ∀ y' ∈ K, ∀ p ∈ L, ∀ p' ∈ L,
      ‖b y p - b y' p'‖ ≤ C * (‖G y - G y'‖ + ‖p - p'‖) := by
  letI : CompactSpace (G '' K) := isCompact_iff_compactSpace.mp
    (cotangentCompact_ambient_isCompact hG.1 hK)
  letI : CompactSpace L := isCompact_iff_compactSpace.mp hL
  have hloc := compactAugmentedCoefficient_locallyLipschitz hG hK hb
  obtain ⟨C, hC⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact
    (isCompact_univ : IsCompact (Set.univ : Set ((G '' K) × L))) hloc.locallyLipschitzOn
  obtain ⟨B, hB⟩ := ((isCompact_univ : IsCompact (Set.univ : Set ((G '' K) × L))).image
    hloc.continuous).isBounded.exists_norm_le
  have heq (y : CotangentPoint M) (hy : y ∈ K) (p : P) (hp : p ∈ L) :
      compactAugmentedCoefficient G b K L (⟨G y, ⟨y, hy, rfl⟩⟩, ⟨p, hp⟩) = b y p := by
    dsimp [compactAugmentedCoefficient]
    rw [compactImmersionPoint_eq hG.2.1 y hy]
  refine ⟨C, max B 0, C.2, le_max_right _ _, ?_, ?_⟩
  · intro y hy p hp
    exact (hB _ ⟨(⟨G y, ⟨y, hy, rfl⟩⟩, ⟨p, hp⟩), Set.mem_univ _, heq y hy p hp⟩).trans
      (le_max_left _ _)
  intro y hy y' hy' p hp p' hp'
  have hh := hC.dist_le_mul (⟨G y, ⟨y, hy, rfl⟩⟩, ⟨p, hp⟩) (Set.mem_univ _)
    (⟨G y', ⟨y', hy', rfl⟩⟩, ⟨p', hp'⟩) (Set.mem_univ _)
  rw [heq y hy p hp, heq y' hy' p' hp', dist_eq_norm] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left (by
    simp only [Prod.dist_eq, Subtype.dist_eq, dist_eq_norm]
    exact max_le_add_of_nonneg (norm_nonneg _) (norm_nonneg _)) C.2)

end Yau.Blueprint.V02WallTaylorProof
