import Yau.Proofs.F01ControlledBackground
import Yau.Proofs.F01OpenOperators
import Yau.Proofs.F01ConformalLeviBound
import Yau.Proofs.F01ConformalGradientBudget

/-! Uniform differential estimates on the actual connected approximation
manifolds, directly from the original controlled exhaustion. -/
noncomputable section
open Set TopologicalSpace
open scoped Matrix ComplexOrder
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Blueprint
variable {n : ℕ} {M : ComplexManifold n}

def approximatingScalar (M : ComplexManifold n) (u : M.Carrier → ℝ) (hu : SmoothFn u)
    (o : M.Carrier) (L : ℝ) (ho : u o < L) :
    (sublevelManifold M u hu o L ho).Carrier → ℝ :=
  conformalScalar (fun x => u x.val) L

def approximatingBaseMetric (M : ComplexManifold n) (g : HermitianField M)
    (u : M.Carrier → ℝ) (hu : SmoothFn u) (o : M.Carrier) (L : ℝ) (ho : u o < L) :
    HermitianField (sublevelManifold M u hu o L ho) :=
  openRestrictedField M (sublevelOpens M u hu o L) (sublevelComponent_isConnected ho) g

theorem approximatingMetric_eq_conformalBase (g : HermitianField M)
    (u : M.Carrier → ℝ) (hu : SmoothFn u) (o : M.Carrier) (L : ℝ) (ho : u o < L) :
    approximatingMetric M g u hu o L ho = conformalField
      (approximatingBaseMetric M g u hu o L ho) (approximatingScalar M u hu o L ho) := rfl

theorem controlled_conformal_gradient_levi (X : KahlerManifold n) (o : Pt X)
    (u : Pt X → ℝ) (hu : ControlledExhaustion X o u) :
    ∃ A : ℝ, 0 < A ∧ ∃ B : ℝ, 0 < B ∧ ∀ (L : ℝ) (ho : u o < L),
      ∀ x : (sublevelManifold X.manifold u hu.1 o L ho).Carrier,
        gradNormSq (approximatingMetric X.manifold X.metric.form u hu.1 o L ho)
          (approximatingScalar X.manifold u hu.1 o L ho) x ≤ A ^ 2 / L ^ 2 ∧
        (levi (approximatingScalar X.manifold u hu.1 o L ho) x -
          ((-(B / L ^ 2) : ℝ) : ℂ) •
            gMat (approximatingMetric X.manifold X.metric.form u hu.1 o L ho) x).PosSemidef ∧
        (((B / L ^ 2 : ℝ) : ℂ) •
          gMat (approximatingMetric X.manifold X.metric.form u hu.1 o L ho) x -
            levi (approximatingScalar X.manifold u hu.1 o L ho) x).PosSemidef := by
  obtain ⟨C, hC, hc⟩ := hu.2.2.2
  obtain ⟨D, hD, hd⟩ := conformalProfile_weighted_derivative_bounds
  obtain ⟨B, hB, hb⟩ := conformalScalar_universal_levi_bound C hC
  refine ⟨D * C, mul_pos hD hC, B, hB, ?_⟩
  intro L ho x
  let N := sublevelManifold X.manifold u hu.1 o L ho
  let g0 : HermitianField N := approximatingBaseMetric X.manifold X.metric.form u hu.1 o L ho
  let u0 : N.Carrier → ℝ := fun a => u a.val
  have hu0 : SmoothFn u0 := smoothFn_openRestriction X.manifold
    (sublevelOpens X.manifold u hu.1 o L) (sublevelComponent_isConnected ho) hu.1
  have hgrad (a : N.Carrier) : gradNormSq g0 u0 a ≤ C ^ 2 := by
    calc
      gradNormSq g0 u0 a = gradNormSq X.metric.form u a.val :=
        openRestriction_gradNormSq X.manifold (sublevelOpens X.manifold u hu.1 o L)
          (sublevelComponent_isConnected ho) X.metric.form u a
      _ ≤ C ^ 2 := (hc a.val).2.2.1
  have hlevi (a : N.Carrier) :
      (levi u0 a - ((-(C / u0 a) : ℝ) : ℂ) • gMat g0 a).PosSemidef ∧
      (((C / u0 a : ℝ) : ℂ) • gMat g0 a - levi u0 a).PosSemidef := by
    have he : levi u0 a = levi u a.val :=
      openRestriction_levi X.manifold (sublevelOpens X.manifold u hu.1 o L)
        (sublevelComponent_isConnected ho) u a
    have hm : gMat g0 a = gMat X.metric.form a.val :=
      openRestrictedField_gMat X.manifold (sublevelOpens X.manifold u hu.1 o L)
        (sublevelComponent_isConnected ho) X.metric.form a
    have hlo : (levi u a.val - ((-(C / u0 a) : ℝ) : ℂ) • gMat X.metric.form a.val).PosSemidef := by
      simpa only [u0, HermLE, Complex.ofReal_neg, Complex.ofReal_div] using (hc a.val).2.2.2.1
    have hhi : (((C / u0 a : ℝ) : ℂ) • gMat X.metric.form a.val - levi u a.val).PosSemidef :=
      (hc a.val).2.2.2.2
    have helo := congrArg₂ (fun A D : Matrix (Fin n) (Fin n) ℂ =>
      A - ((-(C / u0 a) : ℝ) : ℂ) • D) he hm
    have hehi := congrArg₂ (fun A D : Matrix (Fin n) (Fin n) ℂ =>
      ((C / u0 a : ℝ) : ℂ) • D - A) he hm
    exact ⟨helo.symm ▸ hlo, hehi.symm ▸ hhi⟩
  have hL : 0 < L := lt_of_lt_of_le (by norm_num) ((hu.2.2.1 o).trans ho.le)
  have hxpos : 0 < u0 x := lt_of_lt_of_le (by norm_num) (hu.2.2.1 x.val)
  have hxL : u0 x < L := sublevelManifold_point_level X.manifold u hu.1 o L ho x
  have hgb := conformalScalar_gradient_bound_of_weighted_first g0 u0 hu0 hL x hxL
    (hgrad x) (hd (u0 x / L) ⟨(div_pos hxpos hL).le, (div_lt_one hL).mpr hxL⟩).1
  exact ⟨hgb, hb n N g0 u0 hu0 hgrad hlevi L hL x hxpos hxL⟩

end Yau.NodeProofs.F01Aux
