import Yau.Proofs.V02SprayChartSource
import Yau.Proofs.V02FlowNativeCharts

/-! Enlarge the intrinsic disc compact by all prescribed center coordinates.
The same actual spray then has a common tube for every allowed center. -/

open scoped Manifold Topology ContDiff
open Set Metric

noncomputable section
namespace Yau.Blueprint.V02Proof
open Yau Yau.Blueprint V03Proof V02FlowProof

variable {n : ℕ} {M : ComplexManifold n}

theorem cotangentCompact_union_chartImage
    {K : Set (CotangentPoint M)} (hK : CotangentCompact K)
    (x₀ : M.Carrier) {C₀ : Set (CotangentCoord n)} (hC₀ : IsCompact C₀)
    (hC₀T : C₀ ⊆ cotangentTarget x₀) :
    CotangentCompact (K ∪ cotangentChartInv x₀ '' C₀) := by
  obtain ⟨r, x, C, hC, hKeq⟩ := hK
  let x' : Fin (r + 1) → M.Carrier := Fin.cases x₀ x
  let C' : Fin (r + 1) → Set (CotangentCoord n) := Fin.cases C₀ C
  refine ⟨r + 1, x', C', Fin.cases ⟨hC₀, hC₀T⟩ (fun i => hC i), ?_⟩
  ext y
  constructor
  · intro hy
    rcases hy with hy | hy
    · rw [hKeq] at hy
      obtain ⟨i, hi⟩ := mem_iUnion.mp hy
      exact mem_iUnion.mpr ⟨i.succ, hi⟩
    · exact mem_iUnion.mpr ⟨0, hy⟩
  · intro hy
    obtain ⟨i, hi⟩ := mem_iUnion.mp hy
    have hh : ∀ j : Fin (r + 1), y ∈ cotangentChartInv (x' j) '' C' j →
        y ∈ K ∪ cotangentChartInv x₀ '' C₀ :=
      Fin.cases (fun h => Or.inr h) (fun j h => Or.inl (by
        rw [hKeq]
        exact mem_iUnion.mpr ⟨j, h⟩))
    exact hh i hi

def realizationCompact {q : ℕ} {X : KahlerManifold n} (d : VariationData X q)
    (K : Set (CotangentPoint X.manifold)) (Kc : Set (CotangentCoord n × ℝ)) :
    Set (CotangentPoint X.manifold) :=
  K ∪ cotangentChartInv d.chart '' (Prod.fst '' Kc)

theorem realizationCompact_isCompact
    {q : ℕ} {X : KahlerManifold n} {d : VariationData X q} (hd : VariationSetup d)
    {K : Set (CotangentPoint X.manifold)} (hK : CotangentCompact K)
    {Kc : Set (CotangentCoord n × ℝ)} (hKc : IsCompact Kc)
    (hKcC : Kc ⊆ interior (centerCylinder d)) : CotangentCompact (realizationCompact d K Kc) := by
  apply cotangentCompact_union_chartImage hK d.chart (hKc.image continuous_fst)
  rintro z ⟨p, hp, rfl⟩
  exact (hd.2.2.2.2.2.2.2.1.2.2.1 (interior_subset (hKcC hp))).1

theorem realizationCompact_center_mem
    {q : ℕ} {X : KahlerManifold n} (d : VariationData X q)
    (K : Set (CotangentPoint X.manifold)) {Kc : Set (CotangentCoord n × ℝ)}
    {p : CotangentCoord n × ℝ} (hp : p ∈ Kc) :
    cotangentChartInv d.chart p.1 ∈ realizationCompact d K Kc :=
  Or.inr (mem_image_of_mem _ (mem_image_of_mem Prod.fst hp))

theorem closed_chart_piece_mem_spray_union
    {N : ℕ} (x : Fin N → M.Carrier) (a : Fin N → CotangentCoord n)
    {δ : ℝ} (hδ : 0 < δ) {U : Set (NativeCotangentPoint M)}
    (hU : U = ⋃ j, nativeCotangentChartBall (x j) (a j) (2 * δ))
    (j : Fin N) {u : CotangentCoord n} (hu : u ∈ closedBall (a j) δ) :
    NativeCotangentPoint.mk (cotangentChartInv (x j) u) ∈ U := by
  rw [hU]
  exact mem_iUnion.mpr ⟨j, u, (closedBall_subset_ball (by linarith : δ < 2 * δ)) hu, rfl⟩

end Yau.Blueprint.V02Proof
