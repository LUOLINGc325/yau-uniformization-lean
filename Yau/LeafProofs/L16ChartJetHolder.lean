import Yau.LeafProofs.L16ChartCoefficientHolder

open MeasureTheory Filter Set
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic
local instance chartJetHolder_firstGroup {n : ℕ} : NormedAddCommGroup (Space n →L[ℝ] Space n) := inferInstance
local instance chartJetHolder_firstSpace {n : ℕ} : NormedSpace ℝ (Space n →L[ℝ] Space n) := inferInstance
local instance chartJetHolder_secondGroup {n : ℕ} : NormedAddCommGroup (Space n →L[ℝ] Space n →L[ℝ] Space n) := inferInstance
local instance chartJetHolder_secondSpace {n : ℕ} : NormedSpace ℝ (Space n →L[ℝ] Space n →L[ℝ] Space n) := inferInstance
local instance chartJetHolder_dualGroup {n : ℕ} : NormedAddCommGroup (Space n →L[ℝ] ℝ) := inferInstance
local instance chartJetHolder_dualSpace {n : ℕ} : NormedSpace ℝ (Space n →L[ℝ] ℝ) := inferInstance
local instance chartJetHolder_hessianGroup {n : ℕ} : NormedAddCommGroup (Space n →L[ℝ] Space n →L[ℝ] ℝ) := inferInstance
local instance chartJetHolder_hessianSpace {n : ℕ} : NormedSpace ℝ (Space n →L[ℝ] Space n →L[ℝ] ℝ) := inferInstance

/-- Holder control of the complete nonlinear Hessian formula, including
    the original first derivative times the chart's curvature. -/
theorem holderBound_chartSecondJet {n : ℕ} {α J A0 H0 : ℝ} {Q : Set (Point n)}
    {L : Point n → Space n →L[ℝ] Space n}
    {B : Point n → Space n →L[ℝ] Space n →L[ℝ] Space n}
    {A : Point n → Space n →L[ℝ] ℝ}
    {H : Point n → Space n →L[ℝ] Space n →L[ℝ] ℝ}
    (hL : HolderBound α Q L J) (hB : HolderBound α Q B J)
    (hA : HolderBound α Q A A0) (hH : HolderBound α Q H H0) :
    HolderBound α Q (fun p => chartSecondJet (L p) (B p) (A p) (H p)) (4*H0*J^2+2*A0*J) := by
  let C := ContinuousLinearMap.compL ℝ (Space n) (Space n) ℝ
  have hC : ‖C‖ ≤ 1 := ContinuousLinearMap.norm_compL_le ℝ (Space n) (Space n) ℝ
  have hCf : ‖C.flip‖ ≤ 1 := by rw [ContinuousLinearMap.opNorm_flip]; exact hC
  have hRightCon (v : Space n →L[ℝ] Space n) : ‖C.flip v‖ ≤ ‖v‖ := by
    exact (C.flip.le_opNorm v).trans
      ((mul_le_mul_of_nonneg_right hCf (norm_nonneg v)).trans_eq (one_mul _))
  have hLeftCon (v : Space n →L[ℝ] ℝ) : ‖C v‖ ≤ ‖v‖ := by
    exact (C.le_opNorm v).trans
      ((mul_le_mul_of_nonneg_right hC (norm_nonneg v)).trans_eq (one_mul _))
  have hRight := holderBound_comp_linear_contraction C.flip hRightCon hL
  have hLeft := holderBound_comp_linear_contraction C hLeftCon hA
  have hPull := holderBound_clm_comp hRight (holderBound_clm_comp hH hL)
  have hCurvature := holderBound_clm_comp hLeft hB
  have hSum := holderBound_add hPull hCurvature
  convert hSum using 1
  · rfl
  · ring

/-- Compact convex chart buffers give true bounded Lipschitz finite jets
    and hence parabolic Holder budgets before any solution is selected. -/
theorem compact_spatial_chart_jet_holder {n : ℕ} {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    {V K : Set (Space n)} (hV : IsOpen V) (hK : IsCompact K) (hConv : Convex ℝ K)
    (hKV : K ⊆ V) {ψ : Space n → Space n} (hψ : ContDiffOn ℝ 3 ψ V) :
    ∃ C : ℝ, 0 < C ∧ (∀ x ∈ K, ∀ y ∈ K, ‖ψ x-ψ y‖ ≤ C*‖x-y‖) ∧
      ∀ T : ℝ, HolderBound α (cylinder K 0 T) (fun p => fderiv ℝ ψ p.1) C ∧
        HolderBound α (cylinder K 0 T) (fun p => fderiv ℝ (fderiv ℝ ψ) p.1) C := by
  obtain ⟨M,hM,hBound⟩ := compact_actual_three_jet_bound hV hK hKV hψ
  refine ⟨2*M,by positivity,?_,?_⟩
  · intro x hx y hy
    exact (chart_actual_two_jet_lipschitz hV hConv hKV hψ hBound hx hy).1.trans
      (mul_le_mul_of_nonneg_right (by linarith : M ≤ 2*M) (norm_nonneg _))
  · intro T
    exact ⟨holderBound_spatial_lipschitz_field hα hα1 hM.le (fun x hx => (hBound x hx).1)
        (fun x hx y hy => (chart_actual_two_jet_lipschitz hV hConv hKV hψ hBound hx hy).2.1),
      holderBound_spatial_lipschitz_field hα hα1 hM.le (fun x hx => (hBound x hx).2.1)
        (fun x hx y hy => (chart_actual_two_jet_lipschitz hV hConv hKV hψ hBound hx hy).2.2)⟩

/-- Every genuine jet of a nonlinear spatial pullback has its actual
    local Holder budget. The lower-jet output keeps its own small input
    factor, independently of the highest-jet Schauder budget. -/
theorem chart_pullback_full_jet_holder {n : ℕ} {α T K L0 J L : ℝ}
    (hα : 0 ≤ α) (hL : 0 ≤ L) {S V : Set (Space n)} (hV : IsOpen V) (hSV : S ⊆ V)
    {ψ : Space n → Space n} (hψ : ContDiffOn ℝ 3 ψ V)
    (hLip : ∀ x ∈ S, ∀ y ∈ S, ‖ψ x-ψ y‖ ≤ L*‖x-y‖)
    (hDψ : HolderBound α (cylinder S 0 T) (fun p => fderiv ℝ ψ p.1) J)
    (hDDψ : HolderBound α (cylinder S 0 T) (fun p => fderiv ℝ (fderiv ℝ ψ) p.1) J)
    {u : Point n → ℝ} (hu : SchauderBound α (cylinder univ 0 T) u K)
    (huLow : HolderBound α (cylinder univ 0 T) (fun p => (u p,spatialD u p)) L0) :
    let w := chartSpaceTimePullback ψ u
    C2 (cylinder S 0 T) w ∧
      HolderBound α (cylinder S 0 T) w (L0*(1+L^α)) ∧
      HolderBound α (cylinder S 0 T) (spatialD w) (2*(L0*(1+L^α))*J) ∧
      HolderBound α (cylinder S 0 T) (spatialDD w)
        (4*(K*(1+L^α))*J^2+2*(L0*(1+L^α))*J) ∧
      HolderBound α (cylinder S 0 T) (timeD (cylinder S 0 T) w) (K*(1+L^α)) ∧
      HolderBound α (cylinder S 0 T) (fun p => (w p,spatialD w p))
        ((L0*(1+L^α))*(1+2*J)) := by
  let w := chartSpaceTimePullback ψ u
  have hMap : MapsTo ψ S univ := mapsTo_univ _ _
  have hC2 : C2 (cylinder S 0 T) w := c2_chartSpaceTimePullback hV hSV hψ hMap hu.1
  have hLow := holderBound_spatial_lipschitz_pullback hα hL ψ hMap hLip huLow
  have hValue : HolderBound α (cylinder S 0 T) w (L0*(1+L^α)) := holderBound_fst hLow
  have hOriginalGrad := holderBound_snd hLow
  have hHigh := holderBound_spatial_lipschitz_pullback hα hL ψ hMap hLip hu.2.2.2.1
  have hTime := holderBound_spatial_lipschitz_pullback hα hL ψ hMap hLip hu.2.2.2.2
  have hψAt (p : Point n) (hp : p ∈ cylinder S 0 T) : ContDiffAt ℝ 3 ψ p.1 :=
    hψ.contDiffAt (hV.mem_nhds (hSV hp.1))
  have huAt (p : Point n) (hp : p ∈ cylinder S 0 T) :
      ContDiffAt ℝ 2 (fun x => u (x,p.2)) (ψ p.1) :=
    hu.1.2.2.2.2.1 (ψ p.1,p.2) ⟨mem_univ _,hp.2⟩
  have hGrad : HolderBound α (cylinder S 0 T) (spatialD w) (2*(L0*(1+L^α))*J) :=
    holderBound_congr_on (holderBound_clm_comp hOriginalGrad hDψ) (fun p hp =>
      (spatialD_chartSpaceTimePullback p ((hψAt p hp).differentiableAt (by norm_num))
        ((huAt p hp).differentiableAt (by norm_num))).symm)
  have hHess : HolderBound α (cylinder S 0 T) (spatialDD w)
      (4*(K*(1+L^α))*J^2+2*(L0*(1+L^α))*J) :=
    holderBound_congr_on (holderBound_chartSecondJet hDψ hDDψ hOriginalGrad hHigh) (fun p hp =>
      (spatialDD_chartSpaceTimePullback p ((hψAt p hp).of_le (by norm_num)) (huAt p hp)).symm)
  have hTimeActual : HolderBound α (cylinder S 0 T) (timeD (cylinder S 0 T) w) (K*(1+L^α)) :=
    holderBound_congr_on hTime (fun p hp =>
      (timeD_chartSpaceTimePullback ψ u hp.1 (mem_univ _)).symm)
  refine ⟨hC2,hValue,hGrad,hHess,hTimeActual,?_⟩
  have hJ : 0 ≤ J := hDψ.1
  have hV0 : 0 ≤ L0*(1+L^α) := hValue.1
  have hB0 : 0 ≤ (L0*(1+L^α))*(1+2*J) := by positivity
  have hVBig : L0*(1+L^α) ≤ (L0*(1+L^α))*(1+2*J) := by nlinarith
  have hGBig : 2*(L0*(1+L^α))*J ≤ (L0*(1+L^α))*(1+2*J) := by nlinarith
  refine ⟨hB0,?_,?_⟩
  · intro p hp
    exact max_le ((hValue.2.1 p hp).trans hVBig) ((hGrad.2.1 p hp).trans hGBig)
  · intro p hp q hq
    have hW : 0 ≤ holderWeight α p q := by dsimp only [holderWeight]; positivity
    exact max_le ((hValue.2.2 p hp q hq).trans (mul_le_mul_of_nonneg_right hVBig hW))
      ((hGrad.2.2 p hp q hq).trans (mul_le_mul_of_nonneg_right hGBig hW))

/-- Actual finite chart geometry supplies common local full-jet budgets,
    while the lower pair keeps a separate bound linear in its own input.
    The single geometric constant precedes time and every function. -/
theorem compact_chart_pullback_full_jet_budget {n : ℕ} {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1) {V K : Set (Space n)}
    (hV : IsOpen V) (hK : IsCompact K) (hConv : Convex ℝ K) (hKV : K ⊆ V)
    {ψ : Space n → Space n} (hψ : ContDiffOn ℝ 3 ψ V) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Set (Space n)) (T K0 L0 : ℝ) (u : Point n → ℝ), S ⊆ K →
      SchauderBound α (cylinder univ 0 T) u K0 →
      HolderBound α (cylinder univ 0 T) (fun p => (u p,spatialD u p)) L0 →
      let w := chartSpaceTimePullback ψ u
      C2 (cylinder S 0 T) w ∧
        HolderBound α (cylinder S 0 T) w (C*(K0+L0)) ∧
        HolderBound α (cylinder S 0 T) (spatialD w) (C*(K0+L0)) ∧
        HolderBound α (cylinder S 0 T) (spatialDD w) (C*(K0+L0)) ∧
        HolderBound α (cylinder S 0 T) (timeD (cylinder S 0 T) w) (C*(K0+L0)) ∧
        HolderBound α (cylinder S 0 T) (fun p => (w p,spatialD w p)) (C*L0) := by
  obtain ⟨J,hJ,hLip,hJets⟩ := compact_spatial_chart_jet_holder hα hα1 hV hK hConv hKV hψ
  let W : ℝ := 1+J^α
  let C : ℝ := 1+W+2*W*J+4*W*J^2
  have hW : 0 < W := by dsimp only [W]; positivity
  have hFirst : 0 ≤ 2*W*J := by positivity
  have hSecond : 0 ≤ 4*W*J^2 := by positivity
  have hC : 0 < C := by dsimp only [C]; positivity
  have hWC : W ≤ C := by dsimp only [C]; linarith
  have hFirstC : 2*W*J ≤ C := by dsimp only [C]; linarith
  have hSecondC : 4*W*J^2 ≤ C := by dsimp only [C]; linarith
  have hLowC : W*(1+2*J) ≤ C := by dsimp only [C]; nlinarith
  refine ⟨C,hC,?_⟩
  intro S T K0 L0 u hSK hu huLow
  have hK0 : 0 ≤ K0 := hu.2.1
  have hL0 : 0 ≤ L0 := huLow.1
  have hSub : cylinder S 0 T ⊆ cylinder K 0 T := fun p hp => ⟨hSK hp.1,hp.2⟩
  obtain ⟨hC2,hValue,hGrad,hHess,hTime,hLow⟩ := chart_pullback_full_jet_holder hα.le hJ.le hV
    (hSK.trans hKV) hψ (fun x hx y hy => hLip x (hSK hx) y (hSK hy))
    (holderBound_mono (hJets T).1 hSub) (holderBound_mono (hJets T).2 hSub) hu huLow
  have hKBig : C*K0 ≤ C*(K0+L0) := by nlinarith
  have hLBig : C*L0 ≤ C*(K0+L0) := by nlinarith
  refine ⟨hC2,holderBound_mono_const hValue ?_,holderBound_mono_const hGrad ?_,
    holderBound_mono_const hHess ?_,holderBound_mono_const hTime ?_,holderBound_mono_const hLow ?_⟩
  · exact ((mul_le_mul_of_nonneg_left hWC hL0).trans_eq (mul_comm _ _)).trans hLBig
  · calc
      _ = (2*W*J)*L0 := by ring
      _ ≤ C*L0 := mul_le_mul_of_nonneg_right hFirstC hL0
      _ ≤ _ := hLBig
  · calc
      _ = (4*W*J^2)*K0+(2*W*J)*L0 := by ring
      _ ≤ C*K0+C*L0 := add_le_add (mul_le_mul_of_nonneg_right hSecondC hK0)
        (mul_le_mul_of_nonneg_right hFirstC hL0)
      _ = _ := by ring
  · exact ((mul_le_mul_of_nonneg_left hWC hK0).trans_eq (mul_comm _ _)).trans hKBig
  · calc
      _ = (W*(1+2*J))*L0 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hLowC hL0

end Yau.LeafProofs.L16Aux
