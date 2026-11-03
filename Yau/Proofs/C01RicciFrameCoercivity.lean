import Yau.Proofs.C01MovingFrameNorm

/-! A quantitative initial Ricci bound relative to the same metric
propagates along the actual moving-frame equation. -/

noncomputable section

open scoped Manifold Topology ContDiff Matrix ComplexOrder

namespace Yau.NodeProofs.C01Aux

open Yau Yau.Blueprint

variable {n : ℕ} {X : KahlerManifold n} {o : Pt X}
  {h : Flow X} {U P ρ : STF X}

theorem localizedFlow_ricci_quadratic_bound_of_movingFrame
    (hflow : LocalizedFlow X o h U P ρ) (hjoint : JointPositivity X h) (x : Pt X)
    (W : ℝ → (Fin n → ℂ) →L[ℝ] (Fin n → ℂ)) (a b c : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (hinit : W a = ContinuousLinearMap.id ℝ (Fin n → ℂ))
    (hW : ∀ t ∈ Set.Icc a b, HasDerivAt W ((movingFrameCoefficient h x t).comp (W t)) t)
    (hbound : ∀ u : Fin n → ℂ, c * (star u ⬝ᵥ (gMat (h a) x *ᵥ u)).re ≤
      a * (star u ⬝ᵥ (ricci (h a) x *ᵥ u)).re) :
    ∀ v : Fin n → ℂ, c * (star v ⬝ᵥ (gMat (h b) x *ᵥ v)).re ≤
      b * (star v ⬝ᵥ (ricci (h b) x *ᵥ v)).re := by
  intro v
  obtain ⟨u, hu⟩ := localizedFlow_movingFrame_endpoint_surjective hflow x W a b ha hab hinit hW v
  have hmono := localizedFlow_moving_ricci_weight_monotoneOn hflow hjoint x
    (fun s => W s u) a b ha
    (fun t ht => movingFrame_solution_vector_hasDerivAt x W u t (hW t ht))
  have hcomp := hmono (show a ∈ Set.Icc a b from ⟨le_rfl, hab⟩)
    (show b ∈ Set.Icc a b from ⟨hab, le_rfl⟩) hab
  have hcomp' : a * (star u ⬝ᵥ (ricci (h a) x *ᵥ u)).re ≤
      b * (star v ⬝ᵥ (ricci (h b) x *ᵥ v)).re := by
    simpa only [hinit, ContinuousLinearMap.id_apply, hu] using hcomp
  have hnorm := localizedFlow_moving_metric_norm_eq hflow x (fun s => W s u) a b ha hab
    (fun t ht => movingFrame_solution_vector_hasDerivAt x W u t (hW t ht))
  have hnorm' : (star v ⬝ᵥ (gMat (h b) x *ᵥ v)).re =
      (star u ⬝ᵥ (gMat (h a) x *ᵥ u)).re := by
    simpa only [hinit, ContinuousLinearMap.id_apply, hu] using congrArg Complex.re hnorm
  rw [hnorm']
  exact (hbound u).trans hcomp'

theorem localizedFlow_ricci_relative_bound_of_movingFrame
    (hflow : LocalizedFlow X o h U P ρ) (hjoint : JointPositivity X h) (x : Pt X)
    (W : ℝ → (Fin n → ℂ) →L[ℝ] (Fin n → ℂ)) (a b c : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (hinit : W a = ContinuousLinearMap.id ℝ (Fin n → ℂ))
    (hW : ∀ t ∈ Set.Icc a b, HasDerivAt W ((movingFrameCoefficient h x t).comp (W t)) t)
    (hbound : ∀ u : Fin n → ℂ, c * (star u ⬝ᵥ (gMat (h a) x *ᵥ u)).re ≤
      a * (star u ⬝ᵥ (ricci (h a) x *ᵥ u)).re) :
    HermLE ((c : ℂ) • gMat (h b) x) ((b : ℂ) • ricci (h b) x) := by
  have hA := localizedFlow_ricci_isHermitian hflow x (ha.trans_le hab)
  have hH := (Alignment.Y03Proof.hMat_posDef (h b) x (chartPt x x)
    (mem_extChartAt_target (I := ComplexModel n) x)).isHermitian
  have hherm : ((b : ℂ) • ricci (h b) x - (c : ℂ) • gMat (h b) x).IsHermitian :=
    (hA.smul (by simp [IsSelfAdjoint])).sub (hH.smul (by simp [IsSelfAdjoint]))
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hherm
  intro v
  apply Complex.nonneg_iff.mpr
  refine ⟨?_, (hherm.im_star_dotProduct_mulVec_self v).symm⟩
  have hq := localizedFlow_ricci_quadratic_bound_of_movingFrame
    hflow hjoint x W a b c ha hab hinit hW hbound v
  simpa only [Matrix.sub_mulVec, dotProduct_sub, Complex.sub_re, Matrix.smul_mulVec,
    dotProduct_smul, smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, sub_nonneg] using hq

end Yau.NodeProofs.C01Aux
