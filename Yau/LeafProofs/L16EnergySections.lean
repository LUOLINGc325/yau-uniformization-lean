import Yau.LeafProofs.L16EnergyGraph
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-! Forward Fubini representation by actual spatial L² section classes. -/
open MeasureTheory Filter TopologicalSpace
open scoped Topology
noncomputable section
namespace Yau.LeafProofs.L16Aux

/-- Distances to a dense sequence give a topological embedding. -/
private theorem energy_distance_embedding {E : Type*} [MetricSpace E]
    (d : ℕ → E) (hd : DenseRange d) :
    Topology.IsEmbedding (fun x : E => fun k : ℕ => dist x (d k)) := by
  let D : E → ℕ → ℝ := fun x k => dist x (d k)
  have hc : Continuous D := continuous_pi fun k => continuous_id.dist continuous_const
  refine ⟨Topology.isInducing_iff_nhds.mpr (fun x => ?_), ?_⟩
  · apply le_antisymm (hc.tendsto x).le_comap
    change Tendsto (fun y : E => y) (comap D (𝓝 (D x))) (𝓝 x)
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    obtain ⟨k, hk⟩ := hd.exists_dist_lt x (by positivity : 0 < ε / 4)
    have ht : Tendsto (fun y : E => dist y (d k)) (comap D (𝓝 (D x)))
        (𝓝 (dist x (d k))) :=
      (continuous_apply k).tendsto (D x) |>.comp tendsto_comap
    filter_upwards [ht.eventually_lt_const (by linarith : dist x (d k) < ε / 2)] with y hy
    calc
      dist y x ≤ dist y (d k) + dist (d k) x := dist_triangle _ _ _
      _ < ε := by rw [dist_comm (d k) x]; linarith
  · intro x y hxy
    apply dist_le_zero.mp
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨k, hk⟩ := hd.exists_dist_lt x (by positivity : 0 < ε / 2)
    have he : dist x (d k) = dist y (d k) := congrFun hxy k
    have ht := dist_triangle x (d k) y
    rw [dist_comm (d k) y, ← he] at ht
    linarith

/-- Strong measurability follows from measurable distances to fixed points in a
separable metric space. This statement concerns fixed points only. -/
private theorem energy_aestronglyMeasurable_of_dist
    {α E : Type*} [MeasurableSpace α] {ν : Measure α}
    [MetricSpace E] [SeparableSpace E] [Nonempty E] (F : α → E)
    (hF : ∀ g : E, AEStronglyMeasurable (fun t => dist (F t) g) ν) :
    AEStronglyMeasurable F ν := by
  let d := denseSeq E
  have he := energy_distance_embedding d (denseRange_denseSeq E)
  apply he.aestronglyMeasurable_comp_iff.mp
  apply aestronglyMeasurable_iff_aemeasurable.mpr
  exact aemeasurable_pi_iff.mpr fun k => (hF (d k)).aemeasurable

/-- The actual spatial class, with zero used at times having no L² section. -/
def energyL2Section {α β : Type*} [MeasurableSpace α] (μ : Measure α)
    (f : α × β → ℝ) (t : β) : Lp ℝ 2 μ := by
  classical
  exact if h : MemLp (fun x => f (x,t)) 2 μ then h.toLp (fun x => f (x,t)) else 0

theorem energyL2Section_eq {α β : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α × β → ℝ} {t : β} (h : MemLp (fun x => f (x,t)) 2 μ) :
    energyL2Section μ f t = h.toLp (fun x => f (x,t)) := by
  simp only [energyL2Section, dite_eq_left h]

/-- A product L² function has genuine L² sections at almost every time. -/
theorem energy_memLp_section_ae {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν]
    {f : α × β → ℝ} (hf : MemLp f 2 (μ.prod ν)) :
    ∀ᵐ t ∂ν, MemLp (fun x => f (x,t)) 2 μ := by
  filter_upwards [hf.aestronglyMeasurable.prodMk_right, hf.integrable_sq.prod_left_ae]
    with t hm hi
  exact (memLp_two_iff_integrable_sq hm).mpr hi

/-- Fubini gives measurable distances to each fixed spatial L² class. -/
theorem energyL2Section_dist_aestronglyMeasurable
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν]
    {f : α × β → ℝ} (hf : MemLp f 2 (μ.prod ν)) (g : Lp ℝ 2 μ) :
    AEStronglyMeasurable (fun t => dist (energyL2Section μ f t) g) ν := by
  have hm : AEStronglyMeasurable (fun z : α × β => (f z - g z.1) ^ 2) (μ.prod ν) :=
    (hf.aestronglyMeasurable.sub (Lp.aestronglyMeasurable g).comp_fst).pow 2
  have hi := hm.prod_swap.integral_prod_right'
  apply (Real.continuous_sqrt.comp_aestronglyMeasurable hi).congr
  filter_upwards [energy_memLp_section_ae hf] with t ht
  have he : ‖energyL2Section μ f t - g‖ ^ 2 =
      ∫ x, (f (x,t) - g x) ^ 2 ∂μ := by
    calc
      _ = ‖(ht.sub (Lp.memLp g)).toLp ((fun x => f (x,t)) - (g : α → ℝ))‖ ^ 2 := by
        rw [MemLp.toLp_sub ht (Lp.memLp g), Lp.toLp_coeFn g (Lp.memLp g),
          energyL2Section_eq ht]
      _ = _ := by
        simpa only [sq_abs, Pi.sub_apply] using energy_toLp_norm_sq (ht.sub (Lp.memLp g))
  change Real.sqrt (∫ x, (f (x,t) - g x) ^ 2 ∂μ) = _
  rw [← he, Real.sqrt_sq_eq_abs, abs_norm, dist_eq_norm]

/-- The forward Bochner section bridge for arbitrary separable spatial L².
No measurability of variable representative evaluation is asserted or used. -/
theorem energyL2Section_memLp
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν]
    [SeparableSpace (Lp ℝ 2 μ)]
    {f : α × β → ℝ} (hf : MemLp f 2 (μ.prod ν)) :
    MemLp (energyL2Section μ f) 2 ν := by
  have hm : AEStronglyMeasurable (energyL2Section μ f) ν :=
    energy_aestronglyMeasurable_of_dist _ (energyL2Section_dist_aestronglyMeasurable hf)
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  apply hf.integrable_sq.integral_prod_right.congr
  filter_upwards [energy_memLp_section_ae hf] with t ht
  rw [energyL2Section_eq ht, energy_toLp_norm_sq ht]
  simp only [sq_abs]

/-- The section curve has exactly the original product squared norm. -/
theorem energyL2Section_integral_norm_sq
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν]
    {f : α × β → ℝ} (hf : MemLp f 2 (μ.prod ν)) :
    (∫ t, ‖energyL2Section μ f t‖ ^ 2 ∂ν) = ∫ z, |f z| ^ 2 ∂μ.prod ν := by
  rw [integral_prod_symm _ (by simpa only [sq_abs] using hf.integrable_sq)]
  apply integral_congr_ae
  filter_upwards [energy_memLp_section_ae hf] with t ht
  rw [energyL2Section_eq ht, energy_toLp_norm_sq ht]

/-- Exact forward product/Bochner L² representation, including the raw section class. -/
theorem energyL2Sections_exists
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν]
    [SeparableSpace (Lp ℝ 2 μ)]
    {f : α × β → ℝ} (hf : MemLp f 2 (μ.prod ν)) :
    ∃ F : β → Lp ℝ 2 μ, MemLp F 2 ν ∧
      (∀ᵐ t ∂ν, ∃ ht : MemLp (fun x => f (x,t)) 2 μ,
        ht.toLp (fun x => f (x,t)) = F t) ∧
      (∫ t, ‖F t‖ ^ 2 ∂ν) = ∫ z, |f z| ^ 2 ∂μ.prod ν := by
  refine ⟨energyL2Section μ f, energyL2Section_memLp hf, ?_,
    energyL2Section_integral_norm_sq hf⟩
  filter_upwards [energy_memLp_section_ae hf] with t ht
  exact ⟨ht, (energyL2Section_eq ht).symm⟩

open Yau.Parabolic

/-- Forward section representation for the exact frozen spacetime measure.
Spatial openness and compact closure are unnecessary for this direction. -/
theorem energy_productVolume_sections {n : ℕ} (O : Set (Space n)) (T : ℝ)
    {f : Point n → ℝ} (hf : MemLp f 2 (productVolume O (Set.Ioo 0 T))) :
    ∃ F : ℝ → Lp ℝ 2 (volume.restrict O),
      MemLp F 2 (volume.restrict (Set.Ioo 0 T)) ∧
      (∀ᵐ t ∂volume.restrict (Set.Ioo 0 T),
        ∃ ht : MemLp (fun x => f (x,t)) 2 (volume.restrict O),
          ht.toLp (fun x => f (x,t)) = F t) ∧
      (∫ t, ‖F t‖ ^ 2 ∂volume.restrict (Set.Ioo 0 T)) =
        ∫ z, |f z| ^ 2 ∂productVolume O (Set.Ioo 0 T) := by
  have : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  exact energyL2Sections_exists hf

end Yau.LeafProofs.L16Aux
