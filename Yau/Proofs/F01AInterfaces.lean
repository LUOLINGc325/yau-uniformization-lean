import Yau.Proofs.F01NativeLogDetEvolution

/-! Actual native potential solutions on closed and half-open time slabs.
These transparent propositions assert properties of the supplied metric and
potential; they introduce no additional analytic premise for F01. -/
noncomputable section
open Set
open scoped Matrix ComplexOrder

namespace Yau.NodeProofs.F01Aux
open Yau
variable {n : ℕ} {M : ComplexManifold n}

/-- A genuine closed-slab potential solution, with one finite metric comparison. -/
def NativePotentialSlab (g : HermitianField M) (T : ℝ)
    (h : ℝ → HermitianField M) (U : M.Carrier → ℝ → ℝ) : Prop :=
  h 0 = g ∧ MetricFamilySmooth h (Icc 0 T) ∧
  SmoothSpaceTime U (Icc 0 T) ∧ (∀ x, U x 0 = 0) ∧
  ∃ C : ℝ, 1 ≤ C ∧ ∀ x t, t ∈ Icc 0 T →
    (gMat (h t) x - ((C⁻¹ : ℝ) : ℂ) • gMat g x).PosSemidef ∧
    ((C : ℂ) • gMat g x - gMat (h t) x).PosSemidef ∧
    gMat (h t) x = gMat g x - (t : ℂ) • ricci g x +
      levi (fun y => U y t) x ∧
    HasDerivWithinAt (U x) (flowLogDetRatio g h x t) (Icc 0 T) t

/-- A genuine partial solution with one comparison constant on the entire
half-open interval and actual smooth PDE data on every closed prefix. -/
def NativePartialPotential (g : HermitianField M) (Tstar : ℝ)
    (h : ℝ → HermitianField M) (U : M.Carrier → ℝ → ℝ) : Prop :=
  h 0 = g ∧
  (∀ T, 0 ≤ T → T < Tstar → MetricFamilySmooth h (Icc 0 T)) ∧
  (∀ T, 0 ≤ T → T < Tstar → SmoothSpaceTime U (Icc 0 T)) ∧
  (∀ x, U x 0 = 0) ∧
  (∃ C : ℝ, 1 ≤ C ∧ ∀ x t, t ∈ Ico 0 Tstar →
    (gMat (h t) x - ((C⁻¹ : ℝ) : ℂ) • gMat g x).PosSemidef ∧
    ((C : ℂ) • gMat g x - gMat (h t) x).PosSemidef ∧
    gMat (h t) x = gMat g x - (t : ℂ) • ricci g x +
      levi (fun y => U y t) x) ∧
  ∀ T, 0 ≤ T → T < Tstar → ∀ x t, t ∈ Icc 0 T →
    HasDerivWithinAt (U x) (flowLogDetRatio g h x t) (Icc 0 T) t

end Yau.NodeProofs.F01Aux
