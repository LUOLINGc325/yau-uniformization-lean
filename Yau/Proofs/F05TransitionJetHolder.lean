import Yau.Proofs.F05ActualOverlapJets
import Yau.Proofs.F05BootstrapNative
import Yau.Proofs.F05BootstrapSchauderLimit
import Yau.Proofs.F05HolderIntervals
import Yau.LeafProofs.L16ChartJetHolder

/-! Uniform actual closed-jet transport across a fixed compact genuine
transition buffer. The full nonlinear Hessian transformation is retained. -/

open Set
open scoped ContDiff
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem F05_transition_local_jet_holder {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) (i j : Fin A.count) {K : Set (Space n)}
    (hK : IsCompact K) (hConv : Convex ℝ K) (hKV : K ⊆ F05TransitionDomain A i j)
    (hMap : MapsTo (F05Transition A i j) (F05D A i ∩ K) (region (A.normal j) (3/2)))
    {α s : ℝ} (hα : 0 < α) (hα1 : α < 1) (hs : 0 ≤ s) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T P : ℝ) (w : M.Carrier → ℝ → ℝ),
      (∀ k, C2 (F05Q A k T) (pull A k w)) →
      F05RelSchauder α (region (A.normal j) (3/2)) (Icc s T) (pull A j w) P →
      HolderBound α (cylinder (F05D A i∩K) s T)
        (fun z => ((pull A i w z,spatialD (pull A i w) z),
          (spatialDD (pull A i w) z,F05RelT (Icc s T) (pull A i w) z))) (C*P) := by
  letI : NormedAddCommGroup (Space n →L[ℝ] ℝ) := inferInstance
  letI : NormedSpace ℝ (Space n →L[ℝ] ℝ) := inferInstance
  letI : NormedAddCommGroup (Space n →L[ℝ] Space n →L[ℝ] ℝ) := inferInstance
  letI : NormedSpace ℝ (Space n →L[ℝ] Space n →L[ℝ] ℝ) := inferInstance
  obtain ⟨J,hJ,hLip,hJets⟩ := compact_spatial_chart_jet_holder hα hα1
    (F05TransitionDomain_isOpen hA i j) hK hConv hKV
    ((F05Transition_contDiffOn hA i j).of_le (by simp : (3 : ℕ∞ω) ≤ ∞))
  let W := 1+J^α
  let C := 1+W+4*W*J+4*W*J^2
  have hW : 0 < W := by dsimp only [W]; positivity
  have hC : 0 < C := by dsimp only [C]; positivity
  have hWJ : 0 ≤ W*J := mul_nonneg hW.le hJ.le
  have hWJ2 : 0 ≤ W*J^2 := mul_nonneg hW.le (sq_nonneg J)
  have hWC : W ≤ C := by dsimp only [C]; linarith
  have hGC : 2*W*J ≤ C := by dsimp only [C]; linarith
  have hHC : 4*W*J^2+2*W*J ≤ C := by dsimp only [C]; linarith
  refine ⟨C,hC,?_⟩
  intro T P w hw hSch
  have hP : 0 ≤ P := hSch.2.1.1
  have hSourceD (z : Point n) (hz : z ∈ region (A.normal j) (3/2) ×ˢ Icc s T) :
      F05RelD (region (A.normal j) (3/2)) (pull A j w) z = spatialD (pull A j w) z :=
    F05RelD_eq_spatialD (F05_region_uniqueDiffOn (A.normal j) (by norm_num) z.1 hz.1)
      (((hw j).2.2.2.2.1 z ⟨F05_region_mono (by norm_num) hz.1,hs.trans hz.2.1,hz.2.2⟩).differentiableAt (by norm_num))
  have hSourceDD (z : Point n) (hz : z ∈ region (A.normal j) (3/2) ×ˢ Icc s T) :
      F05RelDD (region (A.normal j) (3/2)) (pull A j w) z = spatialDD (pull A j w) z :=
    F05RelDD_eq_spatialDD (F05_region_uniqueDiffOn (A.normal j) (by norm_num)) hz.1
      (fun x hx => (hw j).2.2.2.2.1 (x,z.2) ⟨F05_region_mono (by norm_num) hx,hs.trans hz.2.1,hz.2.2⟩)
  have hLow := holderBound_congr_on hSch.2.1 (fun z hz =>
    congrArg (fun q => (pull A j w z,q)) (hSourceD z hz))
  have hHigh := holderBound_congr_on hSch.2.2.1 hSourceDD
  have hLipS : ∀ x ∈ F05D A i∩K, ∀ y ∈ F05D A i∩K,
      ‖F05Transition A i j x-F05Transition A i j y‖ ≤ J*‖x-y‖ := fun x hx y hy => hLip x hx.2 y hy.2
  have hPullLow := F05_holder_spatial_pullback_interval hα.le hJ.le (F05Transition A i j) hMap hLipS hLow
  have hPullHigh := F05_holder_spatial_pullback_interval hα.le hJ.le (F05Transition A i j) hMap hLipS hHigh
  have hPullTime := F05_holder_spatial_pullback_interval hα.le hJ.le (F05Transition A i j) hMap hLipS hSch.2.2.2
  have hSub : cylinder (F05D A i∩K) s T ⊆ cylinder K s T := fun z hz => ⟨hz.1.2,hz.2⟩
  have hJac := holderBound_mono (F05_spatial_holder_interval (l := s) (r := T) (hJets (T-s)).1) hSub
  have hJac2 := holderBound_mono (F05_spatial_holder_interval (l := s) (r := T) (hJets (T-s)).2) hSub
  have hGrad := holderBound_clm_comp (holderBound_snd hPullLow) hJac
  have hHess := holderBound_chartSecondJet hJac hJac2 (holderBound_snd hPullLow) hPullHigh
  have hOverlap (z : Point n) (hz : z ∈ cylinder (F05D A i∩K) s T) :=
    F05_actual_overlap_jets hA w hw
      (⟨i,j,⟨z.1,hz.1.1⟩,⟨F05Transition A i j z.1,F05_region_mono (by norm_num) (hMap hz.1)⟩,
        ⟨z.2,hs.trans hz.2.1,hz.2.2⟩,(F05Transition_lift hA i j (hKV hz.1.2)).symm⟩ : F05OverlapPoint A T)
  have hValueActual : HolderBound α (cylinder (F05D A i∩K) s T) (pull A i w) (P*W) := by
    apply holderBound_congr_on (holderBound_fst hPullLow)
    intro z hz
    simpa only [F05OverlapPoint.leftPoint,F05OverlapPoint.rightPoint,Prod.eta] using (hOverlap z hz).1.symm
  have hGradActual : HolderBound α (cylinder (F05D A i∩K) s T)
      (spatialD (pull A i w)) (2*(P*W)*J) := by
    apply holderBound_congr_on hGrad
    intro z hz
    simpa only [F05OverlapPoint.leftPoint,F05OverlapPoint.rightPoint,Prod.eta] using (hOverlap z hz).2.2.1.symm
  have hHessActual : HolderBound α (cylinder (F05D A i∩K) s T)
      (spatialDD (pull A i w)) (4*(P*W)*J^2+2*(P*W)*J) := by
    apply holderBound_congr_on hHess
    intro z hz
    simpa only [F05OverlapPoint.leftPoint,F05OverlapPoint.rightPoint,Prod.eta] using (hOverlap z hz).2.2.2.symm
  have hTimeActual : HolderBound α (cylinder (F05D A i∩K) s T)
      (F05RelT (Icc s T) (pull A i w)) (P*W) := by
    apply holderBound_congr_on hPullTime
    intro z hz
    simp only [F05RelT,pull,F05Transition_lift hA i j (hKV hz.1.2)]
  have hValueBound : P*W ≤ C*P := by nlinarith
  have hGradBound : 2*(P*W)*J ≤ C*P := by nlinarith
  have hHessBound : 4*(P*W)*J^2+2*(P*W)*J ≤ C*P := by nlinarith
  exact F05_holderBound_prod_same
    (F05_holderBound_prod_same (holderBound_mono_const hValueActual hValueBound)
      (holderBound_mono_const hGradActual hGradBound))
    (F05_holderBound_prod_same (holderBound_mono_const hHessActual hHessBound)
      (holderBound_mono_const hTimeActual hValueBound))

end Yau.Proofs.F05Aux
