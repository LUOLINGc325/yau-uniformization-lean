import Yau.LeafProofs.L05ABPPeano

noncomputable section
open Filter Set MeasureTheory Asymptotics
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic Yau.LeafProofs.L05Aux

/-- A literal spatial second Peano expansion, independent of any joint space-time differentiability. -/
def autoSpatialPeanoJet {n : ℕ} (f : Space n → ℝ) (x : Space n)
    (l : Space n →L[ℝ] ℝ) (B : Space n →L[ℝ] Space n →L[ℝ] ℝ) : Prop :=
  (∀ v w, B v w=B w v) ∧
    (fun y => f y-f x-l (y-x)-(1/2 : ℝ)*B (y-x) (y-x)) =o[𝓝 x] (fun y => ‖y-x‖^2)

def autoSpaceEuclideanEquiv (n : ℕ) :
    Space n ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ (Space n))) :=
  (Module.finBasis ℝ (Space n)).equivFun.toContinuousLinearEquiv.trans
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (Module.finrank ℝ (Space n)) => ℝ)).symm

theorem auto_spatial_peano_transport {n : ℕ} {f : Space n → ℝ} {x : Space n}
    (h : L01Aux.Peano2At (f ∘ (autoSpaceEuclideanEquiv n).symm) (autoSpaceEuclideanEquiv n x)) :
    ∃ l B, autoSpatialPeanoJet f x l B := by
  let e := autoSpaceEuclideanEquiv n
  change L01Aux.Peano2At (f ∘ e.symm) (e x) at h
  obtain ⟨l,B,hB,hrem⟩ := h
  refine ⟨l.comp e.toContinuousLinearMap,B.bilinearComp e.toContinuousLinearMap e.toContinuousLinearMap,?_,?_⟩
  · intro v w
    exact hB (e v) (e w)
  · have hr := hrem.comp_tendsto (e.continuous.tendsto x)
    simp only [Function.comp_def,e.symm_apply_apply] at hr
    have ho : (fun y => ‖e (y-x)‖^2) =O[𝓝 x] (fun y => ‖y-x‖^2) := by
      simpa only [Pi.pow_apply] using (e.isBigO_sub (𝓝 x) x).norm_norm.pow 2
    change (fun y => f y-f x-l (e y-e x)-(1/2 : ℝ)*B (e y-e x) (e y-e x))
      =o[𝓝 x] (fun y => ‖e y-e x‖^2) at hr
    have hr' := hr.trans_isBigO (by simpa only [map_sub] using ho)
    change (fun y => f y-f x-l (e (y-x))-(1/2 : ℝ)*B (e (y-x)) (e (y-x)))
      =o[𝓝 x] (fun y => ‖y-x‖^2)
    simpa only [map_sub] using hr'

/-- The already proved real Alexandrov theorem is transported on the actual open spatial set. -/
theorem auto_convex_ae_spatial_peano {n : ℕ} {O : Set (Space n)} (hO : IsOpen O)
    {f : Space n → ℝ} (hf : ConvexOn ℝ O f) :
    ∀ᵐ x ∂((volume : Measure (Space n)).restrict O), ∃ l B, autoSpatialPeanoJet f x l B := by
  let e := autoSpaceEuclideanEquiv n
  let U := e.symm ⁻¹' O
  have hU : IsOpen U := hO.preimage e.symm.continuous
  have hConvex : ConvexOn ℝ U (f ∘ e.symm) := hf.comp_linearMap e.symm.toLinearMap
  have hEuclidean := L01Aux.ae_second_peano_on_open U (f ∘ e.symm) hU hConvex
  have hAll := (ae_restrict_iff' hU.measurableSet).mp hEuclidean
  let : (Measure.map e (volume : Measure (Space n))).IsAddHaarMeasure := e.isAddHaarMeasure_map volume
  have hac : Measure.map e (volume : Measure (Space n)) ≪ volume :=
    Measure.absolutelyContinuous_isAddHaarMeasure _ _
  have hMapped := hAll.filter_mono hac.ae_le
  have hSpace := ae_of_ae_map e.continuous.measurable.aemeasurable hMapped
  apply (ae_restrict_iff' hO.measurableSet).mpr
  filter_upwards [hSpace] with x hx hxO
  apply auto_spatial_peano_transport
  exact hx (by simpa only [U,mem_preimage,e.symm_apply_apply] using hxO)

end Yau.LeafProofs.L05AutonomousAux
