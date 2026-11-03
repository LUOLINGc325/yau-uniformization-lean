import Yau.LeafProofs.L23FieldMetricParallelChange
import Yau.LeafProofs.L23FieldMetricCoordinatePairing

/-! Actual frame-valued parallel equations and their invariant gluing. -/
noncomputable section
open Filter
open scoped Topology ContDiff Manifold
namespace Yau.LeafProofs.L23Aux
open L12Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option maxHeartbeats 800000

def IsParallelFrameOn (h : HermitianField M) (γ : ℝ → M.Carrier)
    (P : (u : ℝ) → ComplexVector n →L[ℝ] TangentSpace 𝓘(ℝ, ComplexVector n) (γ u)) (I : Set ℝ) : Prop :=
  ∀ (c : M.Carrier) (t : ℝ), t ∈ I → γ t ∈ (chartAt (ComplexVector n) c).source →
    HasDerivAt (fun u => (realTangentCoords c (γ u)).comp (P u))
      ((chartParallelCoefficient h c γ t).comp ((realTangentCoords c (γ t)).comp (P t))) t

theorem parallelFrameOn_mono (h : HermitianField M) (γ : ℝ → M.Carrier)
    (P : (u : ℝ) → ComplexVector n →L[ℝ] TangentSpace 𝓘(ℝ, ComplexVector n) (γ u))
    {I J : Set ℝ} (H : IsParallelFrameOn h γ P J) (hsub : I ⊆ J) : IsParallelFrameOn h γ P I :=
  fun c t ht hc => H c t (hsub ht) hc

theorem realFrameCLM_comp_realTangentCoords (c y : M.Carrier)
    (hy : y ∈ (chartAt (ComplexVector n) c).source) :
    (realFrameCLM c y).comp (realTangentCoords c y) = ContinuousLinearMap.id ℝ _ := by
  apply ContinuousLinearMap.ext
  intro v
  exact realFrameCLM_realTangentCoords c y hy v

theorem realTangentCoords_comp_realFrameCLM_change (a b y : M.Carrier)
    (ha : y ∈ (chartAt (ComplexVector n) a).source)
    (hb : y ∈ (chartAt (ComplexVector n) b).source) :
    (realTangentCoords b y).comp (realFrameCLM a y) = fderiv ℝ (realChartChange a b) (chartPt a y) := by
  have hz : chartPt a y ∈ chartTarget a :=
    (extChartAt (ComplexModel n) a).map_source (by simpa only [extChartAt_source] using ha)
  have hinv : chartInv a (chartPt a y) = y :=
    (extChartAt (ComplexModel n) a).left_inv (by simpa only [extChartAt_source] using ha)
  have hyb : chartInv a (chartPt a y) ∈ (extChartAt (ComplexModel n) b).source := by
    rw [hinv]
    simpa only [extChartAt_source] using hb
  apply ContinuousLinearMap.ext
  intro v
  have H := realChartChange_fderiv a b hz hyb v
  rw [hinv,← realFrameCLM_apply a y ha v] at H
  exact H.symm

theorem curve_coordinates_change_hasDerivAt
    (γ : ℝ → M.Carrier) (a b : M.Carrier) (t : ℝ) (T : ComplexVector n)
    (hγ : ContinuousAt γ t) (ha : γ t ∈ (chartAt (ComplexVector n) a).source)
    (hb : γ t ∈ (chartAt (ComplexVector n) b).source)
    (hcoord : HasDerivAt (fun u => chartPt a (γ u)) T t) :
    HasDerivAt (fun u => chartPt b (γ u))
      (fderiv ℝ (realChartChange a b) (chartPt a (γ t)) T) t := by
  have hz : chartPt a (γ t) ∈ chartTarget a :=
    (extChartAt (ComplexModel n) a).map_source (by simpa only [extChartAt_source] using ha)
  have hinv : chartInv a (chartPt a (γ t)) = γ t :=
    (extChartAt (ComplexModel n) a).left_inv (by simpa only [extChartAt_source] using ha)
  have hyb : chartInv a (chartPt a (γ t)) ∈ (extChartAt (ComplexModel n) b).source := by
    rw [hinv]
    simpa only [extChartAt_source] using hb
  have H := ((realChartChange_contDiffAt a b hz hyb).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t hcoord
  apply H.congr_of_eventuallyEq
  filter_upwards [hγ.preimage_mem_nhds ((chartAt (ComplexVector n) a).open_source.mem_nhds ha)] with u hu
  change chartPt b (γ u) = chartPt b (chartInv a (chartPt a (γ u)))
  change γ u ∈ (chartAt (ComplexVector n) a).source at hu
  have HI : chartInv a (chartPt a (γ u)) = γ u :=
    (extChartAt (ComplexModel n) a).left_inv (by simpa only [extChartAt_source] using hu)
  rw [HI]

theorem parallelFrameOn_splice (h : HermitianField M) (γ : ℝ → M.Carrier)
    (P Q : (u : ℝ) → ComplexVector n →L[ℝ] TangentSpace 𝓘(ℝ, ComplexVector n) (γ u))
    (a b c d T : ℝ) (HP : IsParallelFrameOn h γ P (Set.Ioo a b))
    (HQ : IsParallelFrameOn h γ Q (Set.Ioo c d))
    (hTP : T ∈ Set.Ioo a b) (hTQ : T ∈ Set.Ioo c d) (heq : P T = Q T) :
    IsParallelFrameOn h γ (fun u => if u ≤ T then P u else Q u) (Set.Ioo a d) := by
  intro z t ht hz
  let ZP : ℝ → ComplexVector n →L[ℝ] ComplexVector n := fun u => (realTangentCoords z (γ u)).comp (P u)
  let ZQ : ℝ → ComplexVector n →L[ℝ] ComplexVector n := fun u => (realTangentCoords z (γ u)).comp (Q u)
  let ZR : ℝ → ComplexVector n →L[ℝ] ComplexVector n :=
    fun u => (realTangentCoords z (γ u)).comp (if u ≤ T then P u else Q u)
  change HasDerivAt ZR ((chartParallelCoefficient h z γ t).comp (ZR t)) t
  by_cases htT : t < T
  · have H := HP z t ⟨ht.1,htT.trans hTP.2⟩ hz
    have HEq : ZR =ᶠ[𝓝 t] ZP := by
      filter_upwards [Iio_mem_nhds htT] with u hu
      change (realTangentCoords z (γ u)).comp (if u ≤ T then P u else Q u) = _
      rw [if_pos hu.le]
    rw [HEq.self_of_nhds]
    exact H.congr_of_eventuallyEq HEq
  · by_cases hTt : T < t
    · have H := HQ z t ⟨hTQ.1.trans hTt,ht.2⟩ hz
      have HEq : ZR =ᶠ[𝓝 t] ZQ := by
        filter_upwards [Ioi_mem_nhds hTt] with u hu
        change (realTangentCoords z (γ u)).comp (if u ≤ T then P u else Q u) = _
        rw [if_neg (not_le.mpr hu)]
      rw [HEq.self_of_nhds]
      exact H.congr_of_eventuallyEq HEq
    · have htEq : t = T := le_antisymm (le_of_not_gt hTt) (le_of_not_gt htT)
      subst t
      have HM : ZP T = ZQ T := by change (realTangentCoords z (γ T)).comp (P T) = _; rw [heq]
      have HLeft := HP z T hTP hz
      have HRight := HQ z T hTQ hz
      change HasDerivAt ZQ ((chartParallelCoefficient h z γ T).comp (ZQ T)) T at HRight
      rw [← HM] at HRight
      have Hpiece := hasDerivAt_splice ZP ZQ T ((chartParallelCoefficient h z γ T).comp (ZP T)) HM HLeft HRight
      have HF : ZR = (fun u => if u ≤ T then ZP u else ZQ u) := by
        funext u
        dsimp only [ZR,ZP,ZQ]
        split_ifs <;> rfl
      rw [HF]
      simpa only [if_pos le_rfl] using Hpiece

theorem parallelFrame_coordinates_contDiffOn_three
    (h : HermitianField M) (hh : MetricSmooth h) (γ : ℝ → M.Carrier)
    (P : (u : ℝ) → ComplexVector n →L[ℝ] TangentSpace 𝓘(ℝ, ComplexVector n) (γ u))
    (I : Set ℝ) (hI : IsOpen I) (HP : IsParallelFrameOn h γ P I) (c : M.Carrier) :
    letI := manifold_realSmooth M
    ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) 3 γ I →
    ContDiffOn ℝ 3 (fun u => (realTangentCoords c (γ u)).comp (P u))
      (I ∩ γ ⁻¹' (chartAt (ComplexVector n) c).source) := by
  letI := manifold_realSmooth M
  intro hγ
  let K := I ∩ γ ⁻¹' (chartAt (ComplexVector n) c).source
  have hK : IsOpen K := hγ.continuousOn.isOpen_inter_preimage hI (chartAt (ComplexVector n) c).open_source
  have hγK : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) 3 γ K := hγ.mono (fun u hu => hu.1)
  have hsource : Set.MapsTo γ K (chartAt (ComplexVector n) c).source := fun u hu => hu.2
  exact linearODE_contDiffOn_three (chartParallelCoefficient h c γ) _ K hK
    (chartParallelCoefficient_contDiffOn_two h hh γ c K hK hγK hsource)
    (fun u hu => HP c u hu.1 hu.2)

end Yau.LeafProofs.L23Aux
