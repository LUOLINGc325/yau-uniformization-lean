import Yau.Proofs.P04PoleWeightModel

noncomputable section
open Set Filter
open scoped Topology ContDiff Manifold

namespace Yau.Proofs.P04Aux
open Yau Yau.LeafProofs
variable {n : ℕ} {M : ComplexManifold n}

def globalPolePart (p : M.Carrier) (χ : ComplexVector n → ℝ) (c ε : ℝ) : M.Carrier → ℝ :=
  L18Aux.chartPushforwardZero p (regularizedPoleModel χ (chartPt p p) c ε)

theorem globalPolePart_smooth (p : M.Carrier) {χ : ComplexVector n → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ chartTarget p)
    (c : ℝ) {ε : ℝ} (hε : 0 < ε) : SmoothFn (globalPolePart p χ c ε) :=
  L18Aux.smoothFn_chartPushforwardZero p (regularizedPoleModel_smooth hχ _ c hε)
    (regularizedPoleModel_compact hc _ c ε) ((regularizedPoleModel_tsupport χ _ c ε).trans hs)

theorem globalPolePart_compact (p : M.Carrier) {χ : ComplexVector n → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ chartTarget p)
    (c : ℝ) {ε : ℝ} (hε : 0 < ε) : HasCompactSupport (globalPolePart p χ c ε) :=
  (L18Aux.chartPushforwardZero_properties p (regularizedPoleModel_smooth hχ _ c hε)
    (regularizedPoleModel_compact hc _ c ε) ((regularizedPoleModel_tsupport χ _ c ε).trans hs)).1

theorem globalPolePart_mono (p : M.Carrier) {χ : ComplexVector n → ℝ}
    (hχ : ∀ z, 0 ≤ χ z) {c ε δ : ℝ} (hc : 0 ≤ c) (hε : 0 < ε) (hεδ : ε ≤ δ)
    (x : M.Carrier) : globalPolePart p χ c ε x ≤ globalPolePart p χ c δ x := by
  classical
  by_cases hx : x ∈ (extChartAt (ComplexModel n) p).source
  · simpa only [globalPolePart,L18Aux.chartPushforwardZero,if_pos hx] using
      regularizedPoleModel_mono hχ (chartPt p p) hc hε hεδ (chartPt p x)
  · simp only [globalPolePart,L18Aux.chartPushforwardZero,if_neg hx,le_refl]

theorem globalPolePart_nonpos (p : M.Carrier) {χ : ComplexVector n → ℝ}
    (hχ : ∀ z, 0 ≤ χ z) {c ρ ε : ℝ} (hc : 0 ≤ c) (hρ : 0 < ρ) (hsmall : 5*ρ^2 < 1)
    (hs : tsupport χ ⊆ Metric.closedBall (chartPt p p) (3*ρ/2))
    (hε : 0 < ε) (hερ : ε ≤ ρ) (x : M.Carrier) : globalPolePart p χ c ε x ≤ 0 := by
  classical
  by_cases hx : x ∈ (extChartAt (ComplexModel n) p).source
  · simpa only [globalPolePart,L18Aux.chartPushforwardZero,if_pos hx] using
      regularizedPoleModel_nonpos hχ (chartPt p p) hc hρ hsmall hs hε hερ (chartPt p x)
  · simp only [globalPolePart,L18Aux.chartPushforwardZero,if_neg hx,le_refl]

def regularizedPoleWeight (p : M.Carrier) (χ : ComplexVector n → ℝ)
    (c k : ℝ) (ψ : M.Carrier → ℝ) (ε : ℝ) (x : M.Carrier) : ℝ :=
  k*ψ x+globalPolePart p χ c ε x

theorem regularizedPoleWeight_smooth (p : M.Carrier) {χ : ComplexVector n → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ chartTarget p)
    (c k : ℝ) {ψ : M.Carrier → ℝ} (hψ : SmoothFn ψ) {ε : ℝ} (hε : 0 < ε) :
    SmoothFn (regularizedPoleWeight p χ c k ψ ε) := by
  intro a
  exact (contDiffOn_const.mul (hψ a)).add (globalPolePart_smooth p hχ hc hs c hε a)

theorem regularizedPoleWeights_antitone (p : M.Carrier) {χ : ComplexVector n → ℝ}
    (hχ : ∀ z, 0 ≤ χ z) {c ρ : ℝ} (hc : 0 ≤ c) (hρ : 0 < ρ)
    (k : ℝ) (ψ : M.Carrier → ℝ) (x : M.Carrier) :
    Antitone (fun j => regularizedPoleWeight p χ c k ψ (poleEpsilon ρ j) x) := by
  intro i j hij
  change k*ψ x+globalPolePart p χ c (poleEpsilon ρ j) x ≤
    k*ψ x+globalPolePart p χ c (poleEpsilon ρ i) x
  apply add_le_add_right
  exact globalPolePart_mono p hχ hc (poleEpsilon_pos hρ j) (poleEpsilon_antitone hρ hij) x

/-- Each fixed regularized change of weight is smooth. Its bounds may depend
on epsilon; no uniform multiplier bound is asserted near the pole. -/
theorem poleMultiplier_smooth {P : M.Carrier → ℝ} (hP : SmoothFn P) :
    SmoothFn (fun x => Real.exp (-P x/2)) := by
  intro a
  exact ((hP a).neg.div_const (2 : ℝ)).exp

theorem poleMultiplier_weight_identity (P Φ : M.Carrier → ℝ) (x : M.Carrier) :
    Real.exp (-P x/2)^2*Real.exp (-Φ x) = Real.exp (-(Φ x+P x)) := by
  rw [pow_two,← Real.exp_add,← Real.exp_add]
  congr 1
  ring

end Yau.Proofs.P04Aux
