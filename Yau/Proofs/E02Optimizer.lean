import Yau.Blueprint.Nodes

open Set Filter
open scoped Topology ContDiff Manifold Matrix ComplexOrder
noncomputable section
namespace Yau.NodeProofs.E02Aux
open Yau Yau.Blueprint

/-- The actual maximizing feasible determinant is the supremum in the
 ORIGINAL definition. Both nonemptiness and its finite upper bound are
 proved before evaluating the conditional supremum. -/
theorem ellipsoidLogDet_eq_log_det_of_max
    {n : ℕ} (X : KahlerManifold n) (h : Flow X) (T : ℝ) (x : Pt X)
    (z : ComplexVector n) (t : ℝ) (B : Herm n)
    (hB : FeasibleEllipsoid X h T x z t B)
    (hMax : ∀ D, FeasibleEllipsoid X h T x z t D → D.det.re ≤ B.det.re) :
    ellipsoidLogDet X h T x z t = Real.log B.det.re := by
  let S : Set ℝ := {d | ∃ D, FeasibleEllipsoid X h T x z t D ∧ d = D.det.re}
  have hMem : B.det.re ∈ S := ⟨B,hB,rfl⟩
  have hNE : S.Nonempty := ⟨B.det.re,hMem⟩
  have hUpper : ∀ d ∈ S, d ≤ B.det.re := by
    rintro d ⟨D,hD,rfl⟩
    exact hMax D hD
  have hBdd : BddAbove S := ⟨B.det.re,hUpper⟩
  have hSup : sSup S = B.det.re := le_antisymm (csSup_le hNE hUpper) (le_csSup hBdd hMem)
  change Real.log (sSup S) = Real.log B.det.re
  exact congrArg Real.log hSup

/-- The gap keeps the original fixed chart and maximizing matrix. -/
theorem volumeGap_eq_of_max
    {n : ℕ} (X : KahlerManifold n) (h : Flow X) (T : ℝ) (x : Pt X)
    (z : ComplexVector n) (t : ℝ) (B : Herm n)
    (hB : FeasibleEllipsoid X h T x z t B)
    (hMax : ∀ D, FeasibleEllipsoid X h T x z t D → D.det.re ≤ B.det.re) :
    volumeGap X h T x z t = -logDet (h t) x z-Real.log B.det.re := by
  unfold volumeGap
  rw [ellipsoidLogDet_eq_log_det_of_max X h T x z t B hB hMax]

/-- Select the ORIGINAL optimizer once, before every small-weight list.
The determinant value is calculated from that same matrix. -/
theorem optimizerContacts_one_matrix
    {n : ℕ} (X : KahlerManifold n) (h : Flow X) (ρ : STF X)
    (hoc : OptimizerContacts X h ρ) {T : ℝ} (hT : 0 < T) (x : Pt X)
    (z : ComplexVector n) (t : ℝ) (hz : z ∈ chartTarget x) (ht : t ∈ Ioo 0 T) :
    ∃ B : Herm n, FeasibleEllipsoid X h T x z t B ∧
      (∀ D, FeasibleEllipsoid X h T x z t D → D.det.re ≤ B.det.re) ∧
      ellipsoidLogDet X h T x z t = Real.log B.det.re ∧
      ∀ ε, 0 < ε → ∃ (m : ℕ) (η : Fin m → ComplexVector n) (α : Fin m → ℝ),
        (∀ i, 0 < α i ∧ α i ≤ ε ∧ envelopeChart h T x (z,η i,t) = 1 ∧
          (star (WithLp.ofLp (η i)) ⬝ᵥ (B*ᵥWithLp.ofLp (η i))).re = 1) ∧
        ∑ i, (α i : ℂ) • Matrix.vecMulVec (WithLp.ofLp (η i))
          (star (WithLp.ofLp (η i))) = B⁻¹ ∧
        ∑ i, α i = n := by
  rcases (hoc T hT x).2 z t hz ht with ⟨_hUnique,_hGap0,_hGapρ,B,hB,hMax,hContacts⟩
  exact ⟨B,hB,hMax,ellipsoidLogDet_eq_log_det_of_max X h T x z t B hB hMax,hContacts⟩

/-- In dimension zero the optimizer determinant is exactly one. No
 nonexistence of a zero-dimensional manifold is used. -/
theorem ellipsoidLogDet_dimension_zero
    (X : KahlerManifold 0) (h : Flow X) (ρ : STF X)
    (hoc : OptimizerContacts X h ρ) {T : ℝ} (hT : 0 < T) (x : Pt X)
    (z : ComplexVector 0) (t : ℝ) (hz : z ∈ chartTarget x) (ht : t ∈ Ioo 0 T) :
    ellipsoidLogDet X h T x z t = 0 := by
  obtain ⟨B,hB,hMax⟩ := ((hoc T hT x).2 z t hz ht).1.exists
  rw [ellipsoidLogDet_eq_log_det_of_max X h T x z t B hB hMax]
  simp only [Matrix.det_isEmpty,Complex.one_re,Real.log_one]

end Yau.NodeProofs.E02Aux
