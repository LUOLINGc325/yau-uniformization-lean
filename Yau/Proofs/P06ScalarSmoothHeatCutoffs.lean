import Yau.Proofs.P06CutoffTailData
import Yau.Proofs.P06ContinuousHeat

/-! Actual compact scalar heat flows for every original metric cutoff.
The zeroth cutoff is normalized exactly as in the Hodge cutoff datum. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff Manifold

namespace Yau.NodeProofs.P06Aux.ScalarSmooth
open Yau Yau.Blueprint Yau.LeafProofs
open L19Aux L18Aux L12Aux

variable {n : ℕ} {M : ComplexManifold n}

def cutoffCore (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (o : M.Carrier)
    (χ : ℕ → M.Carrier → ℝ) (hχ : MetricCutoffFamily g.form o χ)
    (f : M.Carrier → ℝ) (hf : SmoothFn f) (j : ℕ) : ScalarEnergyDomain g μ hμ :=
  ⟨fun x => CutoffTail.cutoffScalar χ j x * f x,
    smoothFn_mul (CutoffTail.cutoffScalar_smooth g o χ hχ j) hf,
    (CutoffTail.cutoffScalar_compact g o χ hχ j).mul_right⟩

@[simp] theorem cutoffCore_apply (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (o : M.Carrier)
    (χ : ℕ → M.Carrier → ℝ) (hχ : MetricCutoffFamily g.form o χ)
    (f : M.Carrier → ℝ) (hf : SmoothFn f) (j : ℕ) (x : M.Carrier) :
    cutoffCore g μ hμ o χ hχ f hf j x = CutoffTail.cutoffScalar χ j x * f x := rfl

theorem cutoffCore_bound (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (o : M.Carrier)
    (χ : ℕ → M.Carrier → ℝ) (hχ : MetricCutoffFamily g.form o χ)
    (f : M.Carrier → ℝ) (hf : SmoothFn f) {C : ℝ}
    (hb : ∀ x, |f x| ≤ C) (j : ℕ) (x : M.Carrier) :
    |cutoffCore g μ hμ o χ hχ f hf j x| ≤ C := by
  obtain ⟨h0,h1⟩ := CutoffTail.cutoffScalar_range g o χ hχ j x
  rw [cutoffCore_apply,abs_mul,abs_of_nonneg h0]
  exact (mul_le_of_le_one_left (abs_nonneg _) h1).trans (hb x)

/-- The actual L19 flow, with its prescribed original value on the initial face. -/
def compactHeat (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (f : ScalarEnergyDomain g μ hμ) : ℝ → M.Carrier → ℝ :=
  fun t x => if t ≤ 0 then f x else
    scalarClassicalHeat (complexDimension_pos M) g hK μ hμ (scalarEnergyDomainL2 g μ hμ f) x t

theorem compactHeat_pos (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (f : ScalarEnergyDomain g μ hμ) {t : ℝ} (ht : 0 < t) :
    compactHeat g hK μ hμ f t = fun x =>
      scalarClassicalHeat (complexDimension_pos M) g hK μ hμ (scalarEnergyDomainL2 g μ hμ f) x t := by
  funext x
  simp only [compactHeat,not_le_of_gt ht,ite_false]

@[simp] theorem compactHeat_zero (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (f : ScalarEnergyDomain g μ hμ) : compactHeat g hK μ hμ f 0 = f := by
  funext x
  simp only [compactHeat,le_refl,ite_true]

theorem compactHeat_smooth (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (f : ScalarEnergyDomain g μ hμ) :
    SmoothSpaceTime (fun x t => compactHeat g hK μ hμ f t x) (Set.Ioi 0) := by
  intro a
  apply (scalarClassicalHeat_smooth (complexDimension_pos M) g hK μ hμ
    (scalarEnergyDomainL2 g μ hμ f) a).congr
  intro p hp
  exact congrFun (compactHeat_pos g hK μ hμ f hp.2) (chartInv a p.1)

theorem compactHeat_hasDerivAt (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (f : ScalarEnergyDomain g μ hμ) (x : M.Carrier) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => compactHeat g hK μ hμ f s x)
      (laplacian g.form (compactHeat g hK μ hμ f t) x) t := by
  rw [compactHeat_pos g hK μ hμ f ht]
  apply (scalarClassicalHeat_hasDerivAt (complexDimension_pos M) g hK μ hμ
    (scalarEnergyDomainL2 g μ hμ f) x ht).congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds ht] with s hs
  exact congrFun (compactHeat_pos g hK μ hμ f hs) x

theorem compactHeat_bound (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (f : ScalarEnergyDomain g μ hμ) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ x, |f x| ≤ C) (x : M.Carrier) (t : ℝ) :
    |compactHeat g hK μ hμ f t x| ≤ C := by
  by_cases ht : t ≤ 0
  · simpa only [compactHeat,ite_true,ht] using hb x
  · rw [compactHeat_pos g hK μ hμ f (lt_of_not_ge ht)]
    apply scalarClassicalHeat_linf (complexDimension_pos M) g hK μ hμ
      (scalarEnergyDomainL2 g μ hμ f) hC _ x (lt_of_not_ge ht)
    filter_upwards [scalarEnergyDomainL2_coe g μ hμ f] with y hy
    rw [hy]
    exact hb y

theorem compactHeat_uniform_initial (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (f : ScalarEnergyDomain g μ hμ) (ε : ℝ) (hε : 0 < ε) :
    ∃ τ > 0, ∀ t, 0 < t → t < τ → ∀ x,
      |compactHeat g hK μ hμ f t x - f x| < ε := by
  obtain ⟨K,hK0,hLap⟩ := scalarCompactLaplacian_bounded g μ hμ f
  refine ⟨ε / (K+1),div_pos hε (by linarith),?_⟩
  intro t ht htτ x
  rw [compactHeat_pos g hK μ hμ f ht]
  have hb := scalarClassicalHeat_compact_initial_bound (complexDimension_pos M)
    g hK μ hμ f hK0 ht hLap x
  have hlt : t * (K+1) < ε := (lt_div_iff₀ (by linarith : 0 < K+1)).mp htτ
  linarith

/-- Each original scalar cutoff has exactly the same bound as its datum,
including the initial face, and satisfies the computed original heat PDE. -/
theorem cutoffHeat_bound (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ) (o : M.Carrier)
    (χ : ℕ → M.Carrier → ℝ) (hχ : MetricCutoffFamily g.form o χ)
    (f : M.Carrier → ℝ) (hf : SmoothFn f) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ x, |f x| ≤ C) (j : ℕ) (x : M.Carrier) (t : ℝ) :
    |compactHeat g hK μ hμ (cutoffCore g μ hμ o χ hχ f hf j) t x| ≤ C :=
  compactHeat_bound g hK μ hμ _ hC (cutoffCore_bound g μ hμ o χ hχ f hf hb j) x t

end Yau.NodeProofs.P06Aux.ScalarSmooth
