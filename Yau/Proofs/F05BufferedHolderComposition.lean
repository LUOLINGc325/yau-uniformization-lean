import Yau.Proofs.F05BufferedComposition

/-! The same compact supported transition gives a uniform budget for actual
Holder sources, without requiring derivatives or a lateral trace. -/

open Set
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency.types true
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.LeafProofs.L16Aux

theorem F05_buffered_holder_composition_budget {n : ℕ} {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1) {V : Set (Space n)} (hV : IsOpen V)
    {ψ : Space n → Space n} (hψ : ContDiffOn ℝ 3 ψ V)
    {φ : Space n → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hSupport : tsupport φ ⊆ V) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T F : ℝ) (f : Point n → ℝ),
      HolderBound α (cylinder univ 0 T) f F →
      HolderBound α (cylinder univ 0 T)
        (fun p => φ p.1*f (ψ p.1,p.2)) (C*F) := by
  obtain ⟨G,hG,hEqG⟩ := F05_compact_smooth_extension hV hc hSupport hψ
  obtain ⟨R,hR⟩ := hc.isBounded.subset_closedBall (0 : Space n)
  let r : ℝ := 1+|R|
  have hSupportBall : tsupport φ ⊆ Metric.closedBall 0 r :=
    hR.trans (Metric.closedBall_subset_closedBall (by dsimp only [r]; linarith [le_abs_self R]))
  obtain ⟨L,hL,hLip,hJets⟩ := compact_spatial_chart_jet_holder hα hα1 isOpen_univ
    (isCompact_closedBall (0 : Space n) r) (convex_closedBall (0 : Space n) r) (subset_univ _) hG.contDiffOn
  obtain ⟨P,hP,hCutoff⟩ := F05_smooth_compact_spatial_holder hφ hc
  refine ⟨1+2*P*(1+L^α),by positivity,?_⟩
  intro T F f hf
  have hPull := holderBound_spatial_lipschitz_pullback hα.le hL.le G (mapsTo_univ G _)
    hLip hf
  have hCut : HolderBound α (cylinder univ 0 T) (fun p => φ p.1) P :=
    holderBound_mono (hCutoff α hα hα1) (subset_univ _)
  have hLocal : HolderBound α ((Metric.closedBall (0 : Space n) r ×ˢ (univ : Set ℝ)) ∩ cylinder univ 0 T)
      (fun p => f (G p.1,p.2)) (F*(1+L^α)) := by
    apply holderBound_mono hPull
    intro p hp
    exact ⟨hp.1.1,hp.2.2⟩
  have hZero : ∀ p ∈ cylinder univ 0 T,
      p ∉ Metric.closedBall (0 : Space n) r ×ˢ (univ : Set ℝ) → φ p.1 = 0 := by
    intro p hp hOut
    apply image_eq_zero_of_notMem_tsupport
    intro hMem
    exact hOut ⟨hSupportBall hMem,mem_univ _⟩
  have hProduct := holderBound_smul_cutoff_extension hCut hLocal hZero
  have hFunctions : (fun p : Point n => φ p.1 • f (G p.1,p.2)) =
      (fun p : Point n => φ p.1*f (ψ p.1,p.2)) := by
    funext p
    by_cases hp : φ p.1 = 0
    · simp only [hp,zero_smul,zero_mul]
    · rw [hEqG (subset_tsupport φ hp),smul_eq_mul]
  rw [hFunctions] at hProduct
  apply holderBound_mono_const hProduct
  nlinarith [hf.1]

end Yau.Proofs.F05Aux
