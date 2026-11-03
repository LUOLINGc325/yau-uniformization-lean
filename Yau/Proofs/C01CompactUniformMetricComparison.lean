import Yau.Proofs.C01LocalUniformMetricComparison

/-! A finite genuine chart cover makes time continuity of the metric
uniform on each original compact set, for all tangent directions. -/

noncomputable section

open scoped Manifold Topology ContDiff Matrix ComplexOrder

namespace Yau.NodeProofs.C01Aux

open Yau Yau.Blueprint Filter

variable {n : ℕ} {X : KahlerManifold n} {o : Pt X}
  {h : Flow X} {U P ρ : STF X}

theorem localizedFlow_compact_uniform_metric_comparison
    (hflow : LocalizedFlow X o h U P ρ) (K : Set (Pt X)) (hK : IsCompact K)
    (a : ℝ) (ha : 0 ≤ a) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ s in 𝓝[Set.Ici 0] a, ∀ y ∈ K, ∀ v : ComplexVector n,
      |matrixQuadraticReal (gMat (h s) y) v - matrixQuadraticReal (gMat (h a) y) v| ≤
        ε * matrixQuadraticReal (gMat (h a) y) v := by
  classical
  choose O hO hxO hb using
    (fun x : Pt X => localizedFlow_local_uniform_metric_comparison hflow x a ha ε hε)
  have hcover : K ⊆ ⋃ x, O x := fun x _ => Set.mem_iUnion.mpr ⟨x, hxO x⟩
  obtain ⟨F, hF⟩ := hK.elim_finite_subcover O hO hcover
  have hall : ∀ᶠ s in 𝓝[Set.Ici 0] a, ∀ y ∈ F, ∀ x ∈ O y, ∀ v : ComplexVector n,
      |matrixQuadraticReal (gMat (h s) x) v - matrixQuadraticReal (gMat (h a) x) v| ≤
        ε * matrixQuadraticReal (gMat (h a) x) v :=
    (eventually_all_finset F).mpr (fun y _ => hb y)
  filter_upwards [hall] with s hs
  intro x hx v
  obtain ⟨y, hy⟩ := Set.mem_iUnion.mp (hF hx)
  obtain ⟨hyF, hyO⟩ := Set.mem_iUnion.mp hy
  exact hs y hyF x hyO v

theorem localizedFlow_compact_uniform_normSq_comparison
    (hflow : LocalizedFlow X o h U P ρ) (K : Set (Pt X)) (hK : IsCompact K)
    (a : ℝ) (ha : 0 ≤ a) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ s in 𝓝[Set.Ici 0] a, ∀ y ∈ K, ∀ v : TangentVector X.manifold y,
      |hermitianNormSq (h s y) v - hermitianNormSq (h a y) v| ≤
        ε * hermitianNormSq (h a y) v := by
  filter_upwards [localizedFlow_compact_uniform_metric_comparison hflow K hK a ha ε hε] with s hs
  intro y hy v
  let u : ComplexVector n := tangentSpaceCastModel (ComplexModel n) y v
  have hchart : chartVec y y u = v := by
    rw [Yau.LeafProofs.L12Aux.chartVec_self]
    exact (tangentSpaceCastModel (ComplexModel n) y).symm_apply_apply v
  have hq (t : ℝ) : matrixQuadraticReal (gMat (h t) y) u = hermitianNormSq (h t y) v := by
    simpa only [matrixQuadraticReal, hchart] using center_metric_quadratic_eq_normSq (h t) y u
  have hv := hs y hy u
  rw [hq s, hq a] at hv
  exact hv

theorem localizedFlow_compact_uniform_speedSq_comparison
    (hflow : LocalizedFlow X o h U P ρ) (K : Set (Pt X)) (hK : IsCompact K)
    (a : ℝ) (ha : 0 ≤ a) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∀ᶠ s in 𝓝[Set.Ici 0] a, ∀ y ∈ K, ∀ v : TangentVector X.manifold y,
      (1 - ε)^2 * (2 * hermitianNormSq (h a y) v) ≤ 2 * hermitianNormSq (h s y) v ∧
      2 * hermitianNormSq (h s y) v ≤ (1 + ε)^2 * (2 * hermitianNormSq (h a y) v) := by
  filter_upwards [localizedFlow_compact_uniform_normSq_comparison hflow K hK a ha ε hε] with s hs
  intro y hy v
  obtain ⟨hlo, hhi⟩ := abs_le.mp (hs y hy v)
  have hq := hermitianNormSq_nonneg (h a y) v
  have hεq : 0 ≤ ε * hermitianNormSq (h a y) v := mul_nonneg hε.le hq
  have hsquare : ε ^ 2 * hermitianNormSq (h a y) v ≤ ε * hermitianNormSq (h a y) v :=
    mul_le_mul_of_nonneg_right (by nlinarith) hq
  constructor <;> nlinarith [mul_nonneg (sq_nonneg ε) hq]

end Yau.NodeProofs.C01Aux
