import Yau.LeafProofs.L16NonlinearChartCalculus
import Yau.LeafProofs.L16LocalizedClassicalEquation

open MeasureTheory Filter Set
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic
local instance relativeCutoff_dualGroup {n : ℕ} : NormedAddCommGroup (Space n →L[ℝ] ℝ) := inferInstance
local instance relativeCutoff_dualSpace {n : ℕ} : NormedSpace ℝ (Space n →L[ℝ] ℝ) := inferInstance
local instance relativeCutoff_hessianGroup {n : ℕ} : NormedAddCommGroup (Space n →L[ℝ] Space n →L[ℝ] ℝ) := inferInstance
local instance relativeCutoff_hessianSpace {n : ℕ} : NormedSpace ℝ (Space n →L[ℝ] Space n →L[ℝ] ℝ) := inferInstance

/-- Spatial cutoff extension across artificial chart edges works relative to
    any fixed spatial set. In particular the genuine closed half-space face
    is retained rather than zero-extended. -/
theorem c2_spatial_cutoff_relative_extension {n : ℕ} {l r : ℝ} {S V : Set (Space n)}
    (hV : IsOpen V) {φ : Space n → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hSupport : tsupport φ ⊆ V) {u : Point n → ℝ}
    (hu : C2 (cylinder (S∩V) l r) u) :
    C2 (cylinder S l r) (fun p => φ p.1*u p) := by
  let Q := cylinder S l r
  let QV := cylinder (S∩V) l r
  let w : Point n → ℝ := fun p => φ p.1*u p
  have hw : C2 QV w := c2_spatial_mul hφ hu
  have hZeros (p : Point n) (hp : p.1 ∉ tsupport φ) :
      w p = 0 ∧ spatialD w p = 0 ∧ spatialDD w p = 0 ∧ timeD Q w p = 0 :=
    spatial_cutoff_jets_zero_of_notMem_tsupport Q φ u hp
  have hGlobalContinuous {E : Type} [NormedAddCommGroup E] (f : Point n → E)
      (hSmall : ContinuousOn f QV) (hZero : ∀ p, p.1 ∉ tsupport φ → f p = 0) :
      ContinuousOn f Q := by
    intro p hp
    by_cases hpSupport : p.1 ∈ tsupport φ
    · have hpV := hSupport hpSupport
      apply (hSmall p ⟨⟨hp.1,hpV⟩,hp.2⟩).mono_of_mem_nhdsWithin
      have hNear : ∀ᶠ q : Point n in 𝓝 p, q.1 ∈ V :=
        (hV.preimage continuous_fst).mem_nhds hpV
      filter_upwards [self_mem_nhdsWithin,hNear.filter_mono nhdsWithin_le_nhds] with q hq hqV
      exact ⟨⟨hq.1,hqV⟩,hq.2⟩
    · have hNear : ∀ᶠ q : Point n in 𝓝 p, q.1 ∉ tsupport φ :=
        (isClosed_tsupport φ).isOpen_compl.preimage continuous_fst |>.mem_nhds hpSupport
      apply (continuousWithinAt_const (b := (0 : E))).congr_of_eventuallyEq _ (hZero p hpSupport)
      filter_upwards [hNear.filter_mono nhdsWithin_le_nhds] with q hq
      exact hZero q hq
  have hTimeSmall : ContinuousOn (timeD Q w) QV := by
    apply hw.2.2.2.1.congr
    intro p hp
    exact timeD_cylinder_change_space w hp.1.1 hp.1
  refine ⟨hGlobalContinuous w hw.1 (fun p hp => (hZeros p hp).1),
    hGlobalContinuous (spatialD w) hw.2.1 (fun p hp => (hZeros p hp).2.1),
    hGlobalContinuous (spatialDD w) hw.2.2.1 (fun p hp => (hZeros p hp).2.2.1),
    hGlobalContinuous (timeD Q w) hTimeSmall (fun p hp => (hZeros p hp).2.2.2),?_,?_⟩
  · intro p hp
    by_cases hpSupport : p.1 ∈ tsupport φ
    · exact hw.2.2.2.2.1 p ⟨⟨hp.1,hSupport hpSupport⟩,hp.2⟩
    · have hSlice : (fun x => w (x,p.2)) =ᶠ[𝓝 p.1] (fun _ : Space n => (0 : ℝ)) := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hpSupport] with x hx
        change φ x*u (x,p.2) = 0
        simp only [Pi.zero_apply] at hx
        rw [hx,zero_mul]
      exact (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq hSlice
  · intro p hp
    by_cases hpSupport : p.1 ∈ tsupport φ
    · have hpV := hSupport hpSupport
      have hh := hw.2.2.2.2.2 p ⟨⟨hp.1,hpV⟩,hp.2⟩
      convert hh using 1
      ext t
      simp only [QV,Parabolic.cylinder,mem_prod,mem_inter_iff,hp.1,hpV,true_and]
    · have hφ0 : φ p.1 = 0 := image_eq_zero_of_notMem_tsupport hpSupport
      have hEq : (fun t => w (p.1,t)) = fun _ : ℝ => (0 : ℝ) := by
        funext t
        change φ p.1*u (p.1,t) = 0
        rw [hφ0,zero_mul]
      rw [hEq]
      exact differentiableWithinAt_const 0

/-- A genuine chart-localized classical pullback extends over the artificial
    chart edge on the same actual model spatial set. -/
theorem c2_chart_cutoff_relative_extension {n : ℕ} {S X V : Set (Space n)} {T : ℝ}
    (hV : IsOpen V) {ψ : Space n → Space n} (hψ : ContDiffOn ℝ 3 ψ V)
    (hMap : MapsTo ψ (S∩V) X) {φ : Space n → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hSupport : tsupport φ ⊆ V) {u : Point n → ℝ} (hu : C2 (cylinder X 0 T) u) :
    C2 (cylinder S 0 T) (fun p => φ p.1*u (ψ p.1,p.2)) :=
  c2_spatial_cutoff_relative_extension hV hφ hSupport
    (c2_chartSpaceTimePullback hV inter_subset_right hψ hMap hu)

end Yau.LeafProofs.L16Aux
