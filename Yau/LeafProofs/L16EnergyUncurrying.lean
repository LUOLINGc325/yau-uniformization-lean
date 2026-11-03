import Yau.LeafProofs.L16EnergySections
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Function.LpSeminorm.Prod
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory Filter
open scoped Topology
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L16Aux

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- A fixed spatial L² representative, restricted by a measurable time set. -/
def energySimpleLift (h : Lp ℝ 2 (μ : Measure α)) (s : Set β) : α × β → ℝ :=
  by classical exact fun p => if p.2 ∈ s then h p.1 else 0

theorem energySimpleLift_memLp {μ : Measure α} {ν : Measure β} [IsFiniteMeasure ν]
    (h : Lp ℝ 2 μ) {s : Set β} (hs : MeasurableSet s) :
    MemLp (energySimpleLift h s) 2 (μ.prod ν) := by
  have hp := ((Lp.memLp h).comp_fst ν).indicator (hs.preimage measurable_snd).nullMeasurableSet
  convert hp using 1
  funext p
  classical
  by_cases ht : p.2 ∈ s <;> simp [energySimpleLift, ht]

omit [MeasurableSpace β] in
theorem energySimpleLift_section {μ : Measure α} (h : Lp ℝ 2 μ) (s : Set β) (t : β) :
    ∃ ht : MemLp (fun x => energySimpleLift h s (x,t)) 2 μ,
      ht.toLp (fun x => energySimpleLift h s (x,t)) = s.indicator (fun _ => h) t := by
  classical
  by_cases ht : t ∈ s
  · have hp : MemLp (fun x => energySimpleLift h s (x,t)) 2 μ := by
      simpa only [energySimpleLift, ht, ↓reduceIte] using Lp.memLp h
    refine ⟨hp, ?_⟩
    simpa only [energySimpleLift, ht, ↓reduceIte, Set.indicator_of_mem ht] using
      Lp.toLp_coeFn h (Lp.memLp h)
  · have hp : MemLp (fun x => energySimpleLift h s (x,t)) 2 μ := by
      simpa only [energySimpleLift, ht, ↓reduceIte, Pi.zero_def] using (MemLp.zero : MemLp (0 : α → ℝ) 2 μ)
    refine ⟨hp, ?_⟩
    simpa only [energySimpleLift, ht, ↓reduceIte, Set.indicator_of_notMem ht, Pi.zero_def] using
      (MemLp.toLp_zero (MemLp.zero : MemLp (0 : α → ℝ) 2 μ))

/-- The Hilbert L² norm is computed using the original raw representative. -/
theorem energyHilbert_toLp_norm_sq {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {μ : Measure α} {f : α → E} (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  rw [hx, real_inner_self_eq_norm_sq]

/-- Product almost-everywhere equality gives the correctly ordered section equalities. -/
theorem energy_raw_section_congr_ae {μ : Measure α} {ν : Measure β}
    [SFinite μ] [SFinite ν] {f g : α × β → ℝ} (hfg : f =ᵐ[μ.prod ν] g) :
    ∀ᵐ t ∂ν, (fun x => f (x,t)) =ᵐ[μ] (fun x => g (x,t)) := by
  exact Measure.ae_ae_of_ae_prod
    ((Measure.measurePreserving_swap (μ := ν) (ν := μ)).quasiMeasurePreserving.ae hfg)

section Curry
variable {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν]

/-- The section class depends only on the product almost-everywhere class. -/
theorem energyL2Section_congr_ae {f g : α × β → ℝ}
    (hf : MemLp f 2 (μ.prod ν)) (hg : MemLp g 2 (μ.prod ν))
    (hfg : f =ᵐ[μ.prod ν] g) : energyL2Section μ f =ᵐ[ν] energyL2Section μ g := by
  filter_upwards [energy_memLp_section_ae hf, energy_memLp_section_ae hg,
    energy_raw_section_congr_ae hfg] with t hft hgt ht
  rw [energyL2Section_eq hft, energyL2Section_eq hgt]
  exact hft.toLp_congr hgt ht

theorem energyL2Section_add_ae {f g : α × β → ℝ}
    (hf : MemLp f 2 (μ.prod ν)) (hg : MemLp g 2 (μ.prod ν)) :
    energyL2Section μ (f + g) =ᵐ[ν] energyL2Section μ f + energyL2Section μ g := by
  filter_upwards [energy_memLp_section_ae hf, energy_memLp_section_ae hg]
    with t hft hgt
  have hsum : MemLp (fun x => (f + g) (x,t)) 2 μ := hft.add hgt
  rw [energyL2Section_eq hsum]
  change (hft.add hgt).toLp ((fun x => f (x,t)) + (fun x => g (x,t))) = _
  rw [MemLp.toLp_add, Pi.add_apply, energyL2Section_eq hft, energyL2Section_eq hgt]

theorem energyL2Section_smul_ae {f : α × β → ℝ}
    (hf : MemLp f 2 (μ.prod ν)) (c : ℝ) :
    energyL2Section μ (c • f) =ᵐ[ν] c • energyL2Section μ f := by
  filter_upwards [energy_memLp_section_ae hf] with t hft
  have hmul : MemLp (fun x => (c • f) (x,t)) 2 μ := hft.const_smul c
  rw [energyL2Section_eq hmul]
  change (hft.const_smul c).toLp (c • (fun x => f (x,t))) = _
  rw [MemLp.toLp_const_smul, Pi.smul_apply, energyL2Section_eq hft]

variable [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]

/-- The forward Fubini map on the actual quotient L² spaces. -/
def energyL2Curry (f : Lp ℝ 2 (μ.prod ν)) : Lp (Lp ℝ 2 μ) 2 ν :=
  (energyL2Section_memLp (Lp.memLp f)).toLp (energyL2Section μ f)

theorem energyL2Curry_coeFn (f : Lp ℝ 2 (μ.prod ν)) :
    energyL2Curry f =ᵐ[ν] energyL2Section μ f :=
  MemLp.coeFn_toLp (energyL2Section_memLp (Lp.memLp f))

theorem energyL2Curry_add (f g : Lp ℝ 2 (μ.prod ν)) :
    energyL2Curry (f + g) = energyL2Curry f + energyL2Curry g := by
  apply Lp.ext
  filter_upwards [energyL2Curry_coeFn (f + g), energyL2Curry_coeFn f,
    energyL2Curry_coeFn g, Lp.coeFn_add (energyL2Curry f) (energyL2Curry g),
    energyL2Section_congr_ae (Lp.memLp (f + g)) ((Lp.memLp f).add (Lp.memLp g))
      (Lp.coeFn_add f g), energyL2Section_add_ae (Lp.memLp f) (Lp.memLp g)]
    with t hsum hf hg hadd hraw hsec
  simpa only [Pi.add_apply, hsum, hf, hg, hraw, hsec] using hadd.symm

theorem energyL2Curry_smul (c : ℝ) (f : Lp ℝ 2 (μ.prod ν)) :
    energyL2Curry (c • f) = c • energyL2Curry f := by
  apply Lp.ext
  filter_upwards [energyL2Curry_coeFn (c • f), energyL2Curry_coeFn f,
    Lp.coeFn_smul c (energyL2Curry f),
    energyL2Section_congr_ae (Lp.memLp (c • f)) ((Lp.memLp f).const_smul c)
      (Lp.coeFn_smul c f), energyL2Section_smul_ae (Lp.memLp f) c]
    with t hmul hf hsmul hraw hsec
  simpa only [Pi.smul_apply, hmul, hf, hraw, hsec] using hsmul.symm

theorem energyL2Curry_norm (f : Lp ℝ 2 (μ.prod ν)) : ‖energyL2Curry f‖ = ‖f‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [energyL2Curry, energyHilbert_toLp_norm_sq,
    energyL2Section_integral_norm_sq (Lp.memLp f)]
  simpa only [Lp.toLp_coeFn] using (energy_toLp_norm_sq (Lp.memLp f)).symm

/-- The forward section map is a genuine linear isometry. -/
def energyL2CurryIsometry : Lp ℝ 2 (μ.prod ν) →ₗᵢ[ℝ] Lp (Lp ℝ 2 μ) 2 ν where
  toFun := energyL2Curry
  map_add' := energyL2Curry_add
  map_smul' := energyL2Curry_smul
  norm_map' := energyL2Curry_norm

/-- Applying the quotient map to a raw product representative gives its section curve. -/
theorem energyL2Curry_toLp {f : α × β → ℝ} (hf : MemLp f 2 (μ.prod ν)) :
    energyL2Curry (hf.toLp f) =
      (energyL2Section_memLp hf).toLp (energyL2Section μ f) := by
  exact MemLp.toLp_congr _ _
    (energyL2Section_congr_ae (Lp.memLp (hf.toLp f)) hf hf.coeFn_toLp)

/-- Every temporal indicator of a fixed spatial L² class has an explicit joint lift. -/
theorem energyL2Curry_indicator_mem_range [IsFiniteMeasure ν]
    (c : Lp ℝ 2 μ) {s : Set β} (hs : MeasurableSet s) (hνs : ν s < ⊤) :
    ∃ f : Lp ℝ 2 (μ.prod ν),
      energyL2Curry f = (Lp.simpleFunc.indicatorConst 2 hs hνs.ne c : Lp (Lp ℝ 2 μ) 2 ν) := by
  let hf := energySimpleLift_memLp (ν := ν) c hs
  refine ⟨hf.toLp (energySimpleLift c s), ?_⟩
  rw [energyL2Curry_toLp, Lp.simpleFunc.coe_indicatorConst]
  apply Lp.ext
  filter_upwards [MemLp.coeFn_toLp (energyL2Section_memLp hf),
    (indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := hνs.ne) (c := c))]
    with t hleft hright
  rw [hleft, hright]
  obtain ⟨ht, he⟩ := energySimpleLift_section c s t
  rw [energyL2Section_eq ht]
  exact he

/-- Simple Bochner functions are dense, while an isometry from the complete product
L² space has closed range. Thus the actual forward map is onto. -/
theorem energyL2CurryIsometry_surjective [IsFiniteMeasure ν] :
    Function.Surjective (energyL2CurryIsometry (μ := μ) (ν := ν)) := by
  let C := energyL2CurryIsometry (μ := μ) (ν := ν)
  have hclosed : IsClosed {F : Lp (Lp ℝ 2 μ) 2 ν | ∃ f, C f = F} :=
    C.isometry.isClosedEmbedding.isClosed_range
  intro F
  apply Lp.induction (by norm_num : (2 : ENNReal) ≠ ⊤)
    (fun F => ∃ f, C f = F) ?_ ?_ hclosed F
  · intro c s hs hνs
    exact energyL2Curry_indicator_mem_range c hs hνs
  · intro f g hf hg _ hfr hgr
    obtain ⟨fl, hfl⟩ := hfr
    obtain ⟨gl, hgl⟩ := hgr
    refine ⟨fl + gl, ?_⟩
    rw [map_add, hfl, hgl]

/-- Every actual Bochner L² curve has a jointly measurable product representative,
with its original spatial section classes and the exact squared-norm integral. -/
theorem energyL2Uncurry_exists [IsFiniteMeasure ν]
    {U : β → Lp ℝ 2 μ} (hU : MemLp U 2 ν) :
    ∃ u : α × β → ℝ, MemLp u 2 (μ.prod ν) ∧
      (∀ᵐ t ∂ν, ∃ ht : MemLp (fun x => u (x,t)) 2 μ,
        ht.toLp (fun x => u (x,t)) = U t) ∧
      (∫ z, |u z| ^ 2 ∂μ.prod ν) = ∫ t, ‖U t‖ ^ 2 ∂ν := by
  obtain ⟨f, hf⟩ := energyL2CurryIsometry_surjective (hU.toLp U)
  have hcurve : energyL2Section μ f =ᵐ[ν] U :=
    (MemLp.toLp_eq_toLp_iff (energyL2Section_memLp (Lp.memLp f)) hU).mp hf
  refine ⟨f, Lp.memLp f, ?_, ?_⟩
  · filter_upwards [energy_memLp_section_ae (Lp.memLp f), hcurve] with t ht hct
    exact ⟨ht, (energyL2Section_eq ht).symm.trans hct⟩
  · rw [← energyL2Section_integral_norm_sq (Lp.memLp f)]
    apply integral_congr_ae
    exact hcurve.mono fun t ht => congrArg (fun v : Lp ℝ 2 μ => ‖v‖ ^ 2) ht

end Curry

open Yau.Parabolic

/-- Reverse Fubini for the exact frozen spacetime measure. No spatial openness,
compactness, or additional regularity of the Bochner curve is required. -/
theorem energy_productVolume_uncurry {n : ℕ} (O : Set (Space n)) (T : ℝ)
    {U : ℝ → Lp ℝ 2 (volume.restrict O)}
    (hU : MemLp U 2 (volume.restrict (Set.Ioo 0 T))) :
    ∃ u : Point n → ℝ, MemLp u 2 (productVolume O (Set.Ioo 0 T)) ∧
      (∀ᵐ t ∂volume.restrict (Set.Ioo 0 T),
        ∃ ht : MemLp (fun x => u (x,t)) 2 (volume.restrict O),
          ht.toLp (fun x => u (x,t)) = U t) ∧
      (∫ z, |u z| ^ 2 ∂productVolume O (Set.Ioo 0 T)) =
        ∫ t, ‖U t‖ ^ 2 ∂volume.restrict (Set.Ioo 0 T) := by
  have : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  exact energyL2Uncurry_exists hU

end Yau.LeafProofs.L16Aux
