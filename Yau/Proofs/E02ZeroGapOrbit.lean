import Yau.Proofs.E02ActualProductGap
import Yau.Proofs.E02WeightedCoordinates
import Yau.Proofs.E02BaseTimePacking

open Matrix Set
open scoped Topology ContDiff Matrix ComplexOrder
noncomputable section
namespace Yau.NodeProofs.E02Aux
open Yau Yau.Blueprint

/-- A zero actual product gap lies over the ORIGINAL base and time,
and its columns belong to the entire fixed polynomial equality orbit. -/
theorem actual_product_gap_zero_orbit {n m : ℕ}
    (X : KahlerManifold n) (h : Flow X) (ρ : STF X)
    (hoc : OptimizerContacts X h ρ) (T : ℝ) (hT : 0 < T) (x : Pt X)
    (a : ComplexVector n × ℝ) (B₀ : Herm n)
    (hB₀ : FeasibleEllipsoid X h T x a.1 a.2 B₀)
    (hMax₀ : ∀ D, FeasibleEllipsoid X h T x a.1 a.2 D → D.det.re ≤ B₀.det.re)
    (f : ComplexVector n × ℝ → ℝ) (α : Fin m → ℝ) (hα : ∀ i, 0 ≤ α i)
    (M₀ : Rect n m) (hM₀ : (M₀*M₀ᴴ).PosDef) (θ : ℝ) (hθ : 0 < θ)
    (Q : ProductPoint n m) (hz : Q.1 ∈ chartTarget x) (ht : Q.2.1 ∈ Ioo 0 T)
    (hM : (weightedColumns α Q.2.2*(weightedColumns α Q.2.2)ᴴ).PosDef)
    (hTouch : f (Q.1,Q.2.1) ≤ ellipsoidLogDet X h T x Q.1 Q.2.1)
    (hStrict : (Q.1,Q.2.1) ≠ a →
      f (Q.1,Q.2.1) < ellipsoidLogDet X h T x Q.1 Q.2.1)
    (hZero : actualProductGap X h T x f α (rowProjector M₀) θ Q = 0) :
    (Q.1,Q.2.1) = a ∧
      weightedColumns α Q.2.2*(weightedColumns α Q.2.2)ᴴ = B₀⁻¹ ∧
      (weightedColumns α Q.2.2)ᴴ*B₀*weightedColumns α Q.2.2 = rowProjector M₀ := by
  have hUnique := ((hoc T hT x).2 Q.1 Q.2.1 hz ht).1
  obtain ⟨B,hB,hMax⟩ := hUnique.exists
  have hEq := (actual_product_gap_support X h T x f α hα M₀ hM₀ θ hθ Q hz ht hM
    B hB hMax hTouch).2 hZero
  have hBase : (Q.1,Q.2.1) = a := by
    by_contra hNe
    exact (hStrict hNe).ne hEq.1
  have hzEq : Q.1 = a.1 := congrArg Prod.fst hBase
  have htEq : Q.2.1 = a.2 := congrArg Prod.snd hBase
  have hB₀Q : FeasibleEllipsoid X h T x Q.1 Q.2.1 B₀ := by
    rw [hzEq,htEq]
    exact hB₀
  have hMax₀Q : ∀ D, FeasibleEllipsoid X h T x Q.1 Q.2.1 D → D.det.re ≤ B₀.det.re := by
    rw [hzEq,htEq]
    exact hMax₀
  have hBEq : B = B₀ := hUnique.unique ⟨hB,hMax⟩ ⟨hB₀Q,hMax₀Q⟩
  have hGram : weightedColumns α Q.2.2*(weightedColumns α Q.2.2)ᴴ = B₀⁻¹ :=
    hEq.2.1.trans (congrArg Inv.inv hBEq)
  have hInv : (weightedColumns α Q.2.2*(weightedColumns α Q.2.2)ᴴ)⁻¹ = B₀ := by
    rw [hGram,Matrix.nonsing_inv_nonsing_inv _ (hB₀.1.isUnit.map Matrix.detMonoidHom)]
  have hP := hEq.2.2
  change (weightedColumns α Q.2.2)ᴴ*
    (weightedColumns α Q.2.2*(weightedColumns α Q.2.2)ᴴ)⁻¹*
      weightedColumns α Q.2.2 = rowProjector M₀ at hP
  rw [hInv] at hP
  exact ⟨hBase,hGram,hP⟩

end Yau.NodeProofs.E02Aux
