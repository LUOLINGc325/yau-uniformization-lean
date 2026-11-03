import Yau.Proofs.F04SupportedSmoothProfile
import Yau.LeafProofs.L16WeakL2Representation

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold

noncomputable section

namespace Yau.F04Proof

open Yau.Blueprint Yau.Parabolic Yau.LeafProofs.L18Aux

variable {n : ℕ} {M : ComplexManifold n}

/-- A genuine compact spacetime chart test is jointly smooth after its
 actual manifold zero pushforward. The common spatial compact support makes
 every off-chart zero region an open zero region for the whole time family. -/
theorem chartPushforwardZero_smoothSpaceTime (c : M.Carrier)
    {O : Set (Space n)} (hOt : O ⊆ chartTarget c) {I : Set ℝ}
    {φ : Point n → ℝ} (hφ : Test (O ×ˢ I) φ) :
    SmoothSpaceTime (fun y t => chartPushforwardZero c (fun z => φ (z, t)) y) univ := by
  let Kc := Prod.fst '' tsupport φ
  have hKc : IsCompact Kc := hφ.2.1.image continuous_fst
  have hKct : Kc ⊆ chartTarget c := by
    rintro z ⟨p, hp, rfl⟩
    exact hOt (hφ.2.2 hp).1
  let K := chartInv c '' Kc
  have hK : IsCompact K := hKc.image_of_continuousOn
    ((continuousOn_extChartAt_symm (I := ComplexModel n) c).mono hKct)
  have hKs : K ⊆ (extChartAt (ComplexModel n) c).source := by
    rintro y ⟨z, hz, rfl⟩
    exact (extChartAt (ComplexModel n) c).map_target (hKct hz)
  have hZero (t : ℝ) (y : M.Carrier) (hyK : y ∉ K) :
      chartPushforwardZero c (fun z => φ (z, t)) y = 0 := by
    by_cases hy : y ∈ (extChartAt (ComplexModel n) c).source
    · have hp : (chartPt c y, t) ∉ tsupport φ := by
        intro hp
        apply hyK
        exact ⟨chartPt c y, ⟨(chartPt c y, t), hp, rfl⟩, (extChartAt (ComplexModel n) c).left_inv hy⟩
      simp only [chartPushforwardZero, ite_eq_left hy, image_eq_zero_of_notMem_tsupport hp]
    · simp only [chartPushforwardZero, ite_eq_right hy]
  intro b p hp
  have hz : p.1 ∈ chartTarget b := hp.1
  have hInv : ContinuousAt (chartInv b) p.1 :=
    (continuousOn_extChartAt_symm (I := ComplexModel n) b).continuousAt
      ((isOpen_extChartAt_target (I := ComplexModel n) b).mem_nhds hz)
  have hInvP : ContinuousAt (fun q : Point n => chartInv b q.1) p := hInv.comp continuousAt_fst
  by_cases hyK : chartInv b p.1 ∈ K
  · have hys := hKs hyK
    have hTrans : ContDiffAt ℝ ∞ (fun z => chartPt c (chartInv b z)) p.1 :=
      (chartTransition_contDiffAt b c hz hys).restrict_scalars ℝ
    have hComp := hφ.1.contDiffAt.comp p ((hTrans.comp p contDiffAt_fst).prodMk contDiffAt_snd)
    have he : (fun q : Point n => chartPushforwardZero c (fun z => φ (z, q.2)) (chartInv b q.1)) =ᶠ[𝓝 p]
        (fun q => φ (chartPt c (chartInv b q.1), q.2)) := by
      filter_upwards [hInvP.preimage_mem_nhds
        ((isOpen_extChartAt_source (I := ComplexModel n) c).mem_nhds hys)] with q hq
      change chartInv b q.1 ∈ (extChartAt (ComplexModel n) c).source at hq
      simp only [chartPushforwardZero, ite_eq_left hq]
    exact (hComp.congr_of_eventuallyEq he).contDiffWithinAt
  · have he : (fun q : Point n => chartPushforwardZero c (fun z => φ (z, q.2)) (chartInv b q.1)) =ᶠ[𝓝 p]
        (fun _ => (0 : ℝ)) := by
      filter_upwards [hInvP.preimage_mem_nhds (hK.isClosed.isOpen_compl.mem_nhds hyK)] with q hq
      exact hZero q.2 (chartInv b q.1) hq
    exact ((contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq he).contDiffWithinAt

end Yau.F04Proof
