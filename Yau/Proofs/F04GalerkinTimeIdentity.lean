import Yau.Proofs.F04GalerkinEvolution

open MeasureTheory Filter Set TopologicalSpace
open scoped Topology InnerProductSpace ContDiff

noncomputable section

namespace Yau.F04Proof

open Yau.LeafProofs.L16Aux

variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The actual finite integral equations retain the initial trace against C1
 tests that vanish only at the terminal endpoint. -/
theorem variationalGalerkin_time_test_identity {m : ℕ}
    {T C : ℝ} (hT : 0 < T) (hC : 0 ≤ C) (j : V →L[ℝ] H) (e : Fin m → V)
    (he : Orthonormal ℝ (fun i => j (e i)))
    (B : ℝ → V →L[ℝ] V →L[ℝ] ℝ)
    (hB : ∀ t, ‖B t‖ ≤ C) (hcB : ∀ u v, Continuous (fun t => B t u v))
    {F : ℝ → H}
    (hF : MemLp F 2 (volume.restrict (Ioo 0 T)))
    {c : ℝ → EuclideanSpace ℝ (Fin m)} (hc : ContinuousOn c (Icc 0 T))
    (hcEq : ∀ t ∈ Icc 0 T, c t = ∫ s in (0 : ℝ)..t,
      variationalForcing j e (F s)-variationalMatrix e (B s) (c s))
    {η : ℝ → ℝ} (hη : ContDiff ℝ 1 η) (hηT : η T = 0)
    (d : EuclideanSpace ℝ (Fin m)) :
    (∫ t in Ioo 0 T,
      -deriv η t*inner ℝ
        (j (variationalReconstruction e (c t)))
        (j (variationalReconstruction e d)) +
      η t*B t (variationalReconstruction e (c t)) (variationalReconstruction e d)) =
    ∫ t in Ioo 0 T, η t*inner ℝ (F t)
      (j (variationalReconstruction e d)) := by
  let g := fun t => variationalForcing j e (F t)
  let A := fun t => variationalMatrix e (B t)
  let q := fun t => g t-A t (c t)
  have hq : Integrable q (volume.restrict (Ioo 0 T)) :=
    variationalGalerkin_rhs_integrable hT.le hC j e B hB hcB hF hc
  have hqI : IntervalIntegrable q volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hT.le).mpr hq
  have hPrimitive : ∀ t ∈ Icc 0 T,
      c t = (0 : EuclideanSpace ℝ (Fin m))+∫ s in (0 : ℝ)..t, q s := by
    simpa only [zero_add] using hcEq
  have hIBP := finitePrimitive_timeTest_integrationByParts hT hq hPrimitive hη.contDiffOn d
  simp only [hηT,zero_mul,inner_zero_left,mul_zero,add_zero,sub_zero] at hIBP
  have hgI : IntervalIntegrable g volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hT.le).mpr
      ((variationalForcing j e).integrable_comp (hF.integrable (by norm_num)))
  have hAcI : IntervalIntegrable (fun t => A t (c t)) volume 0 T := by
    convert hgI.sub hqI using 1
    funext t
    dsimp only [q]
    abel
  have hGScalar : IntervalIntegrable (fun t => inner ℝ (g t) d) volume 0 T := by
    have h : IntervalIntegrable (fun t => innerSL ℝ d (g t)) volume 0 T :=
      ⟨(innerSL ℝ d).integrable_comp hgI.1,(innerSL ℝ d).integrable_comp hgI.2⟩
    simpa only [innerSL_apply_apply,real_inner_comm] using h
  have hBScalar : IntervalIntegrable (fun t => inner ℝ (A t (c t)) d) volume 0 T := by
    have h : IntervalIntegrable (fun t => innerSL ℝ d (A t (c t))) volume 0 T :=
      ⟨(innerSL ℝ d).integrable_comp hAcI.1,(innerSL ℝ d).integrable_comp hAcI.2⟩
    simpa only [innerSL_apply_apply,real_inner_comm] using h
  have hGi : IntervalIntegrable (fun t => η t*inner ℝ (g t) d) volume 0 T :=
    hGScalar.continuousOn_mul hη.continuous.continuousOn
  have hBi : IntervalIntegrable (fun t => η t*inner ℝ (A t (c t)) d) volume 0 T :=
    hBScalar.continuousOn_mul hη.continuous.continuousOn
  have hCi : IntervalIntegrable (fun t => -deriv η t*inner ℝ (c t) d) volume 0 T :=
    ((hη.continuous_deriv_one.neg.continuousOn).mul
      (hc.inner continuousOn_const)).intervalIntegrable_of_Icc hT.le
  have hRight : (∫ t in (0 : ℝ)..T, η t*inner ℝ (q t) d) =
      (∫ t in (0 : ℝ)..T, η t*inner ℝ (g t) d)-
        ∫ t in (0 : ℝ)..T, η t*inner ℝ (A t (c t)) d := by
    simp only [q,inner_sub_left,mul_sub]
    exact intervalIntegral.integral_sub hGi hBi
  rw [hRight] at hIBP
  have hFinal : (∫ t in (0 : ℝ)..T,
      -deriv η t*inner ℝ (c t) d+η t*inner ℝ (A t (c t)) d) =
        ∫ t in (0 : ℝ)..T, η t*inner ℝ (g t) d := by
    rw [intervalIntegral.integral_add hCi hBi,hIBP]
    ring
  simp only [intervalIntegral.integral_of_le hT.le,integral_Ioc_eq_integral_Ioo] at hFinal
  simpa only [variationalReconstruction_inner j e he,← variationalMatrix_inner,← variationalForcing_inner j,g,A]
    using hFinal

/-- Every vector in each actual finite energy span has lifted coordinates. -/
theorem variationalGalerkin_reconstruction_surjective [SeparableSpace V]
    (j : V →L[ℝ] H) (hj : Function.Injective j) (m : ℕ)
    {w : V} (hw : w ∈ variationalGalerkinSpace V m) :
    ∃ d : EuclideanSpace ℝ (Fin (Module.finrank ℝ (variationalGalerkinPivotSpace j m))),
      variationalReconstruction (variationalGalerkinFamily j hj m) d = w := by
  let b := variationalGalerkinEnergyBasis j hj m
  let wV : variationalGalerkinSpace V m := ⟨w, hw⟩
  let d : EuclideanSpace ℝ (Fin (Module.finrank ℝ (variationalGalerkinPivotSpace j m))) :=
    WithLp.toLp 2 (b.repr wV)
  refine ⟨d, ?_⟩
  have hb := congrArg (fun z : variationalGalerkinSpace V m => (z : V)) (b.sum_repr wV)
  rw [variationalReconstruction_apply]
  change (∑ i, b.repr wV i • (b i : V)) = w
  simpa only [Submodule.coe_sum, Submodule.coe_smul] using hb

end Yau.F04Proof
