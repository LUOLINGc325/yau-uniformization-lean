import Yau.Proofs.F01ExhaustionSquareLevi
import Yau.Proofs.F01ControlledConformalBounds

/-! The square-exhaustion estimate is transported to the actual connected
approximation, where the conformal metric dominates the ambient metric. -/
noncomputable section
open Set
open scoped Matrix ComplexOrder
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Blueprint
variable {n : ℕ}

theorem approximatingMetric_ge_ambient (X : KahlerManifold n) (o : Pt X)
    (u : Pt X → ℝ) (hu : ControlledExhaustion X o u) {L : ℝ} (ho : u o < L)
    (x : (sublevelManifold X.manifold u hu.1 o L ho).Carrier) :
    (gMat (approximatingMetric X.manifold X.metric.form u hu.1 o L ho) x -
      gMat X.metric.form x.val).PosSemidef := by
  have hL : 0 < L := (zero_lt_one.trans_le (hu.2.2.1 o)).trans ho
  have hf : 0 ≤ approximatingScalar X.manifold u hu.1 o L ho x :=
    conformalProfile_nonneg ((div_lt_one hL).mpr
      (sublevelManifold_point_level X.manifold u hu.1 o L ho x))
  have he : 0 ≤ Real.exp (approximatingScalar X.manifold u hu.1 o L ho x) - 1 :=
    sub_nonneg.mpr (Real.one_le_exp_iff.mpr hf)
  have hpos := (LeafProofs.L12Aux.hMat_posDef X.metric.form x.val (chartPt x.val x.val)
    (mem_extChartAt_target x.val)).posSemidef.smul (Complex.zero_le_real.mpr he)
  change (((Real.exp (approximatingScalar X.manifold u hu.1 o L ho x) - 1 : ℝ) : ℂ) •
    gMat X.metric.form x.val).PosSemidef at hpos
  rw [approximatingMetric_eq_conformalBase, conformalField_gMat]
  have hb : gMat (approximatingBaseMetric X.manifold X.metric.form u hu.1 o L ho) x =
      gMat X.metric.form x.val :=
    openRestrictedField_gMat X.manifold (sublevelOpens X.manifold u hu.1 o L)
      (sublevelComponent_isConnected ho) X.metric.form x
  rw [hb]
  convert hpos using 1
  ext i j
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  push_cast
  ring

theorem controlled_approximating_square_levi (X : KahlerManifold n) (o : Pt X)
    (u : Pt X → ℝ) (hu : ControlledExhaustion X o u) :
    ∃ K : ℝ, 0 < K ∧ ∀ (L : ℝ) (ho : u o < L),
      ∀ x : (sublevelManifold X.manifold u hu.1 o L ho).Carrier,
        ((K : ℂ) • gMat (approximatingMetric X.manifold X.metric.form u hu.1 o L ho) x -
          levi (fun y : (sublevelManifold X.manifold u hu.1 o L ho).Carrier =>
            u y.val ^ 2) x).PosSemidef := by
  obtain ⟨K, hK, hb⟩ := controlled_exhaustion_square_levi X o u hu
  refine ⟨K, hK, ?_⟩
  intro L ho x
  have he : levi (fun y : (sublevelManifold X.manifold u hu.1 o L ho).Carrier =>
      u y.val ^ 2) x = levi (fun y => u y ^ 2) x.val :=
    openRestriction_levi X.manifold (sublevelOpens X.manifold u hu.1 o L)
      (sublevelComponent_isConnected ho) (fun y => u y ^ 2) x
  rw [he]
  have hp := (approximatingMetric_ge_ambient X o u hu ho x).smul
    (Complex.zero_le_real.mpr hK.le)
  convert hp.add (hb x.val).2 using 1
  ext i j
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

end Yau.NodeProofs.F01Aux
