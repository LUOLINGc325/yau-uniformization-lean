import Yau.Proofs.F04GalerkinWeakTime
import Yau.Proofs.F04TimeResidualEquation
import Yau.Proofs.F04TerminalTimeTrace

open MeasureTheory Filter Set TopologicalSpace
open scoped Topology InnerProductSpace ContDiff

noncomputable section

namespace Yau.F04Proof

open Yau.LeafProofs.L16HilbertTimeRegularization Yau.LeafProofs.L16LionsTimeTrace
  Yau.LeafProofs.L16Aux

/-- The dense-union time identities and the actual common-a.e. equation give
 the genuine dual-valued terminal-zero weak identity. -/
theorem variational_union_equation_weak_time
    {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [SeparableSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {T C : ℝ} (hT : 0 < T) (j : V →L[ℝ] H)
    (B : ℝ → V →L[ℝ] V →L[ℝ] ℝ) (hB : ∀ t, ‖B t‖ ≤ C)
    (hcB : ∀ u v, Continuous (fun t => B t u v))
    {F : ℝ → H} (hF : MemLp F 2 (volume.restrict (Ioo 0 T)))
    (U : Lp V 2 (volume.restrict (Ioo 0 T))) {R : ℝ → StrongDual ℝ V}
    (hR : MemLp R 2 (volume.restrict (Ioo 0 T)))
    (hEq : ∀ᵐ t ∂volume.restrict (Ioo 0 T), ∀ v : V, R t v + B t (U t) v = inner ℝ (F t) (j v))
    (hUnion : ∀ η : ℝ → ℝ, ContDiff ℝ 1 η → η T = 0 →
      ∀ v ∈ (⋃ m, (variationalGalerkinSpace V m : Set V)),
        (∫ t in Ioo 0 T, -deriv η t * inner ℝ (j (U t)) (j v) + η t * B t (U t) v) =
          ∫ t in Ioo 0 T, η t * inner ℝ (F t) (j v)) :
    ∀ η : ℝ → ℝ, ContDiff ℝ 1 η → η T = 0 →
      (∫ t in Ioo 0 T, deriv η t • hilbertEmbedding j (U t)) =
        -(∫ t in Ioo 0 T, η t • R t) := by
  intro η hη hηT
  have hiU := integrableOn_continuous_smul_test hT.le
    ((hilbertEmbedding j).integrable_comp ((Lp.memLp U).integrable (by norm_num))) hη.continuous_deriv_one
  have hiR := integrableOn_continuous_smul_test hT.le (hR.integrable (by norm_num)) hη.continuous
  let D : StrongDual ℝ V := (∫ t in Ioo 0 T, deriv η t • hilbertEmbedding j (U t)) +
    ∫ t in Ioo 0 T, η t • R t
  have hDz (v : V) (hv : v ∈ (⋃ m, (variationalGalerkinSpace V m : Set V))) : D v = 0 := by
    let ev : StrongDual ℝ V →L[ℝ] ℝ := ContinuousLinearMap.apply ℝ ℝ v
    have hiDscalar : IntegrableOn (fun t => deriv η t * inner ℝ (j (U t)) (j v)) (Ioo 0 T) :=
      ev.integrable_comp hiU
    have hiRscalar : IntegrableOn (fun t => η t * R t v) (Ioo 0 T) := ev.integrable_comp hiR
    have hηLp : MemLp η 2 (volume.restrict (Ioo 0 T)) := by
      rw [restrict_Ioo_eq_restrict_Icc]
      exact continuousOn_memLp_two hη.continuous.continuousOn
    have hiBscalar := variationalTimeForm_integrable B C hB hcB _ hηLp v (Lp.memLp U)
    have hiFscalar : IntegrableOn (fun t => η t * inner ℝ (F t) (j v)) (Ioo 0 T) := by
      simpa only [IntegrableOn, ContinuousLinearMap.comp_apply, innerSL_apply_apply, real_inner_comm (j v)] using
        timeTestFunctional_integrable hηLp (innerSL ℝ (j v)) hF
    have hiNeg : IntegrableOn (fun t => -deriv η t * inner ℝ (j (U t)) (j v)) (Ioo 0 T) := by
      convert hiDscalar.neg using 1
      funext t
      simp only [Pi.neg_apply, neg_mul]
    have hz : (∫ t in Ioo 0 T, deriv η t * inner ℝ (j (U t)) (j v) + η t * R t v) = 0 := by
      calc
        _ = ∫ t in Ioo 0 T, η t * inner ℝ (F t) (j v) -
            (-deriv η t * inner ℝ (j (U t)) (j v) + η t * B t (U t) v) := by
          apply integral_congr_ae
          filter_upwards [hEq] with t ht
          have htEq := congrArg (fun z : ℝ => η t * z) (ht v)
          nlinarith only [htEq]
        _ = (∫ t in Ioo 0 T, η t * inner ℝ (F t) (j v)) -
            ∫ t in Ioo 0 T, -deriv η t * inner ℝ (j (U t)) (j v) + η t * B t (U t) v :=
          integral_sub hiFscalar (hiNeg.add hiBscalar)
        _ = 0 := by rw [hUnion η hη hηT v hv, sub_self]
    change ev (∫ t in Ioo 0 T, deriv η t • hilbertEmbedding j (U t)) +
      ev (∫ t in Ioo 0 T, η t • R t) = 0
    rw [← ev.integral_comp_comm hiU, ← ev.integral_comp_comm hiR]
    change (∫ t in Ioo 0 T, deriv η t * inner ℝ (j (U t)) (j v)) + (∫ t in Ioo 0 T, η t * R t v) = 0
    exact (integral_add hiDscalar hiRscalar).symm.trans hz
  have hAll (v : V) : D v = 0 := (variationalGalerkinSpace_dense_union V).induction hDz
    (isClosed_eq D.continuous continuous_const) v
  have hD : D = 0 := ContinuousLinearMap.ext hAll
  change (∫ t in Ioo 0 T, deriv η t • hilbertEmbedding j (U t)) + (∫ t in Ioo 0 T, η t • R t) = 0 at hD
  exact add_eq_zero_iff_eq_neg.mp hD

end Yau.F04Proof
