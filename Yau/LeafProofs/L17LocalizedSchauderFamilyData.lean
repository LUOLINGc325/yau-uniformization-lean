import Yau.LeafProofs.L17LocalizedSchauderTransportPair

open Set Metric Filter
open scoped Topology ContDiff
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17LocalizedSchauderAux
open Yau.LeafProofs.L17Aux Yau.LeafProofs.L17HolderAux

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

/-- Local finite-order data on the larger unit ball. These are actual
derivatives and actual differences of the local functions. -/
def UnitLocalJetData (P : UniformChartPartition g) (T : ℝ) (k : ℕ) (gamma F : ℝ)
    (f : P.centers → Time T → ComplexVector n → ℝ) : Prop :=
  (∀ p t, ContDiffOn ℝ (k : ℕ∞ω) (f p t) (ball (0 : ComplexVector n) 2)) ∧
  (∀ p t z, z ∈ ball (0 : ComplexVector n) 2 → ∀ j, j ≤ k →
    ‖iteratedFDeriv ℝ j (f p t) z‖ ≤ F) ∧
  ∀ p t s z w, z ∈ ball (0 : ComplexVector n) 2 → w ∈ ball 0 2 → ∀ j, j ≤ k →
    ‖iteratedFDeriv ℝ j (f p t) z-iteratedFDeriv ℝ j (f p s) w‖ ≤
      F*(unitParabolicDistance P.radius (z,t) (w,s))^gamma

def CutoffJetBounds (P : UniformChartPartition g) (k : ℕ) (C : ℝ) : Prop :=
  ∀ p q z, z ∈ ball (0 : ComplexVector n) 2 → ∀ j, j ≤ k+1 →
    ‖iteratedFDeriv ℝ j (unitCutoff P p q) z‖ ≤ C

def TransitionJetBounds (A : BoundedChartFamily g) (k : ℕ) (D : ℝ) : Prop :=
  (∀ (a : ChartScaleIndex M) z, z ∈ A.scaledTransitionDomain a → ∀ j, j ≤ k →
    ‖iteratedFDeriv ℝ j (A.scaledTransitionMap a) z‖ ≤ D) ∧
  ∀ (a : ChartScaleIndex M) z w, segment ℝ z w ⊆ A.scaledTransitionDomain a → ∀ j, j ≤ k →
    ‖iteratedFDeriv ℝ j (A.scaledTransitionMap a) w-iteratedFDeriv ℝ j (A.scaledTransitionMap a) z‖ ≤ D*‖w-z‖

def cutoffUnitFamily (P : UniformChartPartition g) (hρone : P.radius ≤ 1) {T : ℝ}
    (f : P.centers → Time T → ComplexVector n → ℝ) (p : P.centers) (q : M.Carrier)
    (t : Time T) (z : ComplexVector n) : ℝ :=
  unitCutoff P p q z*f p t (P.charts.scaledTransitionMap
    (⟨P.radius,P.radius_pos,hρone⟩,(q,(p : M.Carrier))) z)

theorem cutoffUnitFamily_iteratedFDeriv_zero (P : UniformChartPartition g) (hρone : P.radius ≤ 1)
    {T : ℝ} (f : P.centers → Time T → ComplexVector n → ℝ)
    (p : P.centers) (q : M.Carrier) (t : Time T) {z : ComplexVector n} (hz : z ∈ ball 0 1)
    (hx : P.charts.chart q (P.radius • z) ∉ P.charts.chart p '' closedBall 0 P.radius) (k : ℕ) :
    iteratedFDeriv ℝ k (cutoffUnitFamily P hρone f p q t) z = 0 := by
  have hzero := unitLocalizedTerm_zero_neighborhood P T p q (fun _ => 1) hz hx
  have heq : cutoffUnitFamily P hρone f p q t =ᶠ[𝓝 z] (fun _ => 0) := by
    filter_upwards [hzero] with w hw
    have hh := hw t
    change (P.radius^2)⁻¹ • (unitCutoff P p q w*1) = 0 at hh
    have hχ : unitCutoff P p q w = 0 := by
      simpa only [mul_one] using (smul_eq_zero.mp hh).resolve_left
        (inv_ne_zero (pow_ne_zero _ P.radius_pos.ne'))
    simp only [cutoffUnitFamily,hχ,zero_mul]
  exact (heq.iteratedFDeriv ℝ k).eq_of_nhds.trans (iteratedFDeriv_zero_function k z)

end Yau.LeafProofs.L17LocalizedSchauderAux
