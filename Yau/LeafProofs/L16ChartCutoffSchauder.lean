import Yau.LeafProofs.L16ChartJetHolder
import Yau.LeafProofs.L16CutoffFullHolderExtension

open MeasureTheory Filter Set
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic
local instance chartCutoffSchauder_dualGroup {n : ℕ} : NormedAddCommGroup (Space n →L[ℝ] ℝ) := inferInstance
local instance chartCutoffSchauder_dualSpace {n : ℕ} : NormedSpace ℝ (Space n →L[ℝ] ℝ) := inferInstance
local instance chartCutoffSchauder_hessianGroup {n : ℕ} : NormedAddCommGroup (Space n →L[ℝ] Space n →L[ℝ] ℝ) := inferInstance
local instance chartCutoffSchauder_hessianSpace {n : ℕ} : NormedSpace ℝ (Space n →L[ℝ] Space n →L[ℝ] ℝ) := inferInstance

/-- A genuine compact chart and genuine cutoff turn every actual ambient
    solution into an ambient Schauder patch. The lower-pair bound retains
    its separate small input, and all constants precede the function. -/
theorem compact_chart_cutoff_full_schauder {n : ℕ} {α E : ℝ}
    (hα : 0 < α) (hα1 : α < 1) {V K S : Set (Space n)}
    (hV : IsOpen V) (hK : IsCompact K) (hConv : Convex ℝ K) (hKV : K ⊆ V)
    (hS : IsOpen S) (hSK : S ⊆ K) {ψ : Space n → Space n} (hψ : ContDiffOn ℝ 3 ψ V)
    {φ : Space n → ℝ} (hφ : ContDiff ℝ 2 φ) (hSupport : tsupport φ ⊆ S)
    (hφ0 : HolderBound α (cylinder univ 0 1) (fun p => φ p.1) E)
    (hφ1 : HolderBound α (cylinder univ 0 1) (fun p => fderiv ℝ φ p.1) E)
    (hφ2 : HolderBound α (cylinder univ 0 1) (fun p => fderiv ℝ (fderiv ℝ φ) p.1) E) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T K0 L0 : ℝ) (u : Point n → ℝ), T ≤ 1 →
      SchauderBound α (cylinder univ 0 T) u K0 →
      HolderBound α (cylinder univ 0 T) (fun p => (u p,spatialD u p)) L0 →
      let w := fun p : Point n => φ p.1*u (ψ p.1,p.2)
      SchauderBound α (cylinder univ 0 T) w (C*(K0+L0)) ∧
        HolderBound α (cylinder univ 0 T) (fun p => (w p,spatialD w p)) (C*L0) := by
  obtain ⟨A,hA,hChart⟩ := compact_chart_pullback_full_jet_budget hα hα1 hV hK hConv hKV hψ
  have hE : 0 ≤ E := hφ0.1
  let C : ℝ := 1+8*E*A
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C,hC,?_⟩
  intro T K0 L0 u hT1 hu huLow
  have hK0 : 0 ≤ K0 := hu.2.1
  have hL0 : 0 ≤ L0 := huLow.1
  obtain ⟨hC2,hValue,hGrad,hHess,hTime,hLow⟩ := hChart S T K0 L0 u hSK hu huLow
  have hSub := cylinder_mono_time (n := n) (O := univ) hT1
  have hFull := cutoff_full_jet_holder_extension hS hφ hSupport hC2
    (holderBound_mono hφ0 hSub) (holderBound_mono hφ1 hSub) (holderBound_mono hφ2 hSub)
    hValue hGrad hHess hTime
  have hSmall := cutoff_low_pair_holder_extension hS hφ hSupport hC2
    (holderBound_mono hφ0 hSub) (holderBound_mono hφ1 hSub)
    (holderBound_fst hLow) (holderBound_snd hLow)
  have hSch : SchauderBound α (cylinder univ 0 T)
      (fun p => φ p.1*chartSpaceTimePullback ψ u p) (8*E*(A*(K0+L0))) := by
    refine ⟨hFull.1,hFull.2.1.1,?_,hFull.2.2.2.1,hFull.2.2.2.2⟩
    intro p hp
    exact ⟨by simpa only [Real.norm_eq_abs] using hFull.2.1.2.1 p hp,hFull.2.2.1.2.1 p hp⟩
  have hLowPair : HolderBound α (cylinder univ 0 T)
      (fun p => (φ p.1*chartSpaceTimePullback ψ u p,
        spatialD (fun q => φ q.1*chartSpaceTimePullback ψ u q) p)) (4*E*(A*L0)) := by
    refine ⟨hSmall.2.1.1,?_,?_⟩
    · intro p hp
      exact max_le (hSmall.2.1.2.1 p hp) (hSmall.2.2.2.1 p hp)
    · intro p hp q hq
      exact max_le (hSmall.2.1.2.2 p hp q hq) (hSmall.2.2.2.2 p hp q hq)
  have hFullBudget : 8*E*(A*(K0+L0)) ≤ C*(K0+L0) := by
    calc
      _ = (8*E*A)*(K0+L0) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by dsimp only [C]; linarith) (add_nonneg hK0 hL0)
  have hSmallBudget : 4*E*(A*L0) ≤ C*L0 := by
    calc
      _ = (4*E*A)*L0 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by dsimp only [C]; nlinarith [mul_nonneg hE hA.le]) hL0
  exact ⟨schauderBound_mono_const hSch hFullBudget,holderBound_mono_const hLowPair hSmallBudget⟩

/-- The actual chart patch retains the global zero initial slice. -/
theorem chart_cutoff_initial_zero {n : ℕ} (φ : Space n → ℝ) (ψ : Space n → Space n)
    {u : Point n → ℝ} (h0 : ∀ x, u (x,0) = 0) (x : Space n) :
    φ x*u (ψ x,0) = 0 := by rw [h0,mul_zero]

/-- A physical cutoff keeps the true lateral data: outside its chart source
    it vanishes, and inside the actual frontier is mapped to the actual face. -/
theorem chart_cutoff_lateral_zero {n : ℕ} {O : Set (Space n)} {e : Space n} {T : ℝ}
    (c : OpenPartialHomeomorph (Space n) (Space n)) {φ : Space n → ℝ}
    (hSupport : tsupport φ ⊆ c.source)
    (hFaces : ∀ x ∈ c.source, x ∈ frontier O → inner ℝ e (c x) = 0)
    {u : Point n → ℝ} (hBoundary : ∀ y, inner ℝ e y = 0 → ∀ t ∈ Icc 0 T, u (y,t) = 0) :
    ∀ x ∈ frontier O, ∀ t ∈ Icc 0 T, φ x*u (c x,t) = 0 := by
  intro x hx t ht
  by_cases hφx : φ x = 0
  · rw [hφx,zero_mul]
  · have hxS : x ∈ c.source := hSupport (subset_tsupport φ (Function.mem_support.mpr hφx))
    rw [hBoundary _ (hFaces x hxS hx) t ht,mul_zero]

end Yau.LeafProofs.L16Aux
