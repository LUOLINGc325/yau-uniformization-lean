import Yau.Proofs.D02Fields

/-! Holomorphicity of the actual unconjugated cotangent/field pairing. -/

open scoped Manifold Topology ContDiff Matrix ComplexOrder
open Bundle

noncomputable section
namespace Yau.NodeProofs.D02Aux
open Yau Yau.Blueprint Yau.Blueprint.V03Proof

variable {n : ℕ} {M : ComplexManifold n}

/-- Holomorphic section coordinates in a valid fixed tangent trivialization. -/
theorem fieldCoords_differentiableOn {V : VectorField M} (hV : IsHolomorphicField V)
    (x : M.Carrier) : DifferentiableOn ℂ (fieldCoords V x) (chartTarget x) := by
  let e := trivializationAt (ComplexVector n) (TangentSpace (ComplexModel n)) x
  have hd : MDifferentiableOn (ComplexModel n) (ComplexModel n)
      (fun y => (e (⟨y, V y⟩ : TangentBundle (ComplexModel n) M.Carrier)).2) e.baseSet :=
    (e.mdifferentiableOn_section_baseSet_iff (IB := ComplexModel n)).mp hV.mdifferentiableOn
  have hmap : Set.MapsTo (chartInv x) (chartTarget x) e.baseSet := by
    intro z hz
    change chartInv x z ∈ (chartAt (ComplexVector n) x).source
    simpa only [extChartAt_source, chartInv] using (extChartAt (ComplexModel n) x).map_target hz
  have hc := hd.comp
    ((contMDiffOn_extChartAt_symm (I := ComplexModel n) (n := ∞) x).mdifferentiableOn
      (by simp)) hmap
  apply hc.differentiableOn.congr
  intro z hz
  change tangentCoords x (chartInv x z) (V (chartInv x z)) =
    tangentCoordChange (ComplexModel n) (chartInv x z) x (chartInv x z) (V (chartInv x z))
  exact tangentCoords_eq_coordChange x (chartInv x z)
    ((extChartAt (ComplexModel n) x).map_target hz) _

/-- Evaluation is holomorphic in the genuine induced cotangent chart. -/
theorem fieldEvaluation_differentiableOn_chart {V : VectorField M} (hV : IsHolomorphicField V)
    (x : M.Carrier) :
    DifferentiableOn ℂ (fun p => fieldEvaluation V (cotangentChartInv x p))
      (cotangentTarget x) := by
  have hc : DifferentiableOn ℂ (fun p : CotangentCoord n => fieldCoords V x p.1)
      (cotangentTarget x) := (fieldCoords_differentiableOn hV x).comp
        differentiable_fst.differentiableOn (fun p hp => hp.1)
  have hη (i : Fin n) : Differentiable ℂ (fun p : CotangentCoord n => p.2 i) :=
    (EuclideanSpace.proj i : ComplexVector n →L[ℂ] ℂ).differentiable.comp
      (differentiable_snd : Differentiable ℂ (Prod.snd : CotangentCoord n → ComplexVector n))
  have hsum : DifferentiableOn ℂ
      (fun p : CotangentCoord n => ∑ i, fieldCoords V x p.1 i * p.2 i) (cotangentTarget x) :=
    DifferentiableOn.fun_sum fun i _ =>
      ((EuclideanSpace.proj i : ComplexVector n →L[ℂ] ℂ).differentiable.comp_differentiableOn hc).mul
        (hη i).differentiableOn

  exact hsum.congr fun p hp => fieldEvaluation_chart V x hp

end Yau.NodeProofs.D02Aux
