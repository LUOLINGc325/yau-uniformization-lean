import Yau.Proofs.V04WallErrorQuadraticTerm
import Yau.Proofs.V03MetricSmooth

/-! All mixed derivatives of the actual sesquilinear fiber polynomial in
a fixed chart. The parameter covector is kept in that same chart. -/

set_option maxHeartbeats 2000000
open scoped Manifold Topology ContDiff Matrix ComplexOrder
noncomputable section
namespace Yau.Blueprint.V04Proof.WallErrorAux
open Yau Yau.Blueprint V03Proof

variable {n : ℕ}

def fiberCoordinate (i : Fin n) : CotangentCoord n →L[ℂ] ℂ :=
  (EuclideanSpace.proj i).comp (ContinuousLinearMap.snd ℂ (ComplexVector n) (ComplexVector n))

def complexQuadratic (A : ComplexVector n → Matrix (Fin n) (Fin n) ℂ)
    (p : CotangentCoord n) : ℂ := ∑ a, ∑ b, star (p.2 a) * A p.1 a b * p.2 b

theorem mixedWirt_complexQuadratic
    {A : ComplexVector n → Matrix (Fin n) (Fin n) ℂ} {p : CotangentCoord n}
    (hA : ∀ a b, ContDiffAt ℝ 2 (fun z => A z a b) p.1) (v w : CotangentCoord n) :
    wirt (fun y => wirtBar (complexQuadratic A) y v) p w =
      ∑ a, ∑ b,
        (star (v.2 a) * (wirt (fun z => A z a b) p.1 w.1 * p.2 b + A p.1 a b * w.2 b) +
          star (p.2 a) * (wirt (fun z => wirtBar (fun u => A u a b) z v.1) p.1 w.1 * p.2 b +
            wirtBar (fun z => A z a b) p.1 v.1 * w.2 b)) := by
  let Fst : CotangentCoord n →L[ℂ] ComplexVector n := ContinuousLinearMap.fst ℂ _ _
  have hξ (a : Fin n) : ContDiffAt ℝ 2 (fun z : CotangentCoord n => z.2 a) p :=
    ((fiberCoordinate a).restrictScalars ℝ).contDiff.contDiffAt
  have hCoef (a b : Fin n) : ContDiffAt ℝ 2 (fun z : CotangentCoord n => A z.1 a b) p :=
    (hA a b).comp p (Fst.restrictScalars ℝ).contDiff.contDiffAt
  have hTerm (a b : Fin n) : ContDiffAt ℝ 2
      (fun z : CotangentCoord n => star (z.2 a) * A z.1 a b * z.2 b) p :=
    (((Complex.conjCLE.contDiff.contDiffAt.comp p (hξ a)).mul (hCoef a b)).mul (hξ b))
  unfold complexQuadratic
  rw [mixedWirt_sum Finset.univ (fun a z => ∑ b, star (z.2 a) * A z.1 a b * z.2 b)
    (fun a _ => ContDiffAt.sum fun b _ => hTerm a b) v w]
  apply Finset.sum_congr rfl
  intro a _
  rw [mixedWirt_sum Finset.univ (fun b z => star (z.2 a) * A z.1 a b * z.2 b)
    (fun b _ => hTerm a b) v w]
  apply Finset.sum_congr rfl
  intro b _
  have h := mixedWirt_sesquilinear_term (fiberCoordinate a) (fiberCoordinate b) (hCoef a b) v w
  have hw : wirt (fun z : CotangentCoord n => A z.1 a b) p w =
      wirt (fun z => A z a b) p.1 w.1 :=
    wirt_comp_clm Fst ((hA a b).differentiableAt (by norm_num)) w
  have hm : wirt (fun z => wirtBar (fun u : CotangentCoord n => A u.1 a b) z v) p w =
      wirt (fun z => wirtBar (fun u => A u a b) z v.1) p.1 w.1 :=
    mixedWirt_comp_clm Fst (hA a b) v w
  have hb : wirtBar (fun z : CotangentCoord n => A z.1 a b) p v =
      wirtBar (fun z => A z a b) p.1 v.1 :=
    wirtBar_comp_clm Fst ((hA a b).differentiableAt (by norm_num)) v
  rw [hw, hm, hb] at h
  exact h

end Yau.Blueprint.V04Proof.WallErrorAux
