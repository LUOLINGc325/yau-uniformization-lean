import Yau.Proofs.E02ActualProductGap

open Matrix Set
open scoped Topology ContDiff Matrix ComplexOrder
noncomputable section
namespace Yau.NodeProofs.E02Aux
open Yau Yau.Blueprint

theorem lowerSemicontinuousOn_nonneg_const_mul {D : Type*} [TopologicalSpace D]
    (v : D → ℝ) (S : Set D) (hv : LowerSemicontinuousOn v S)
    (a : ℝ) (ha : 0 ≤ a) : LowerSemicontinuousOn (fun y => a*v y) S := by
  by_cases hZero : a = 0
  · simpa only [hZero,zero_mul] using (lowerSemicontinuousOn_const :
      LowerSemicontinuousOn (fun _ : D => (0:ℝ)) S)
  have hPos : 0 < a := lt_of_le_of_ne ha (fun hEq => hZero hEq.symm)
  intro y hy r hr
  have hThreshold : r/a < v y := (div_lt_iff₀ hPos).mpr (by simpa only [mul_comm] using hr)
  filter_upwards [hv y hy (r/a) hThreshold] with z hz
  simpa only [mul_comm] using (div_lt_iff₀ hPos).mp hz

/-- Lower semicontinuity of the original finite weighted envelope gap
on its actual chart/full-rank domain. Only the comparison cost is C². -/
theorem actualProductGap_lowerSemicontinuousOn {n m : ℕ}
    (X : KahlerManifold n) (h : Flow X) (T : ℝ) (x : Pt X)
    (f : ComplexVector n × ℝ → ℝ) (α : Fin m → ℝ) (hα : ∀ i, 0 ≤ α i)
    (P₀ : Herm m) (θ : ℝ) (O : Set (ProductPoint n m))
    (hDom : ∀ Q ∈ O, Q.1 ∈ chartTarget x ∧ Q.2.1 ∈ Ioo 0 T)
    (hf : ∀ Q ∈ O, ContDiffAt ℝ 2 f (Q.1,Q.2.1))
    (hM : ∀ Q ∈ O, (weightedColumns α Q.2.2*(weightedColumns α Q.2.2)ᴴ).PosDef) :
    LowerSemicontinuousOn (actualProductGap X h T x f α P₀ θ) O := by
  have hEach (i : Fin m) : LowerSemicontinuousOn
      (fun Q : ProductPoint n m => chartEnvelopeReal X h T x (Q.1,Q.2.2 i,Q.2.1)) O :=
    (chartEnvelopeReal_lowerSemicontinuousOn X h T x).comp
      (by fun_prop : Continuous (fun Q : ProductPoint n m => (Q.1,Q.2.2 i,Q.2.1))).continuousOn
      (fun Q hQ => ⟨(hDom Q hQ).1,(hDom Q hQ).2⟩)
  have hSum : LowerSemicontinuousOn
      (fun Q : ProductPoint n m => ∑ i, α i*chartEnvelopeReal X h T x (Q.1,Q.2.2 i,Q.2.1)) O :=
    lowerSemicontinuousOn_sum (fun i _ =>
      lowerSemicontinuousOn_nonneg_const_mul _ O (hEach i) (α i) (hα i))
  have hCost : ContinuousOn (productCostPhysical f α P₀ θ) O :=
    fun Q hQ => (productCostPhysical_contDiffAt f α P₀ θ Q (hf Q hQ) (hM Q hQ)).continuousAt.continuousWithinAt
  exact hSum.add hCost.neg.lowerSemicontinuousOn

end Yau.NodeProofs.E02Aux
