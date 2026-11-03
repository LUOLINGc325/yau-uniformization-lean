import Yau.Proofs.C01MovingFrameCoefficient

/-! Metric norm conservation makes the endpoint of a genuine solution
of the moving-frame equation bijective.  The solution is supplied later
by the independently checked linear ODE existence theorem. -/

noncomputable section

open scoped Manifold Topology ContDiff Matrix ComplexOrder

namespace Yau.NodeProofs.C01Aux

open Yau Yau.Blueprint

variable {n : ℕ} {X : KahlerManifold n} {o : Pt X}
  {h : Flow X} {U P ρ : STF X}

theorem localizedFlow_moving_metric_norm_eq
    (hflow : LocalizedFlow X o h U P ρ) (x : Pt X)
    (v : ℝ → Fin n → ℂ) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hframe : ∀ t ∈ Set.Icc a b, ∀ i,
      HasDerivAt (fun s => v s i) ((movingFrameMatrix h x t *ᵥ v t) i) t) :
    star (v b) ⬝ᵥ (gMat (h b) x *ᵥ v b) =
      star (v a) ⬝ᵥ (gMat (h a) x *ᵥ v a) := by
  have hd (t : ℝ) (ht : t ∈ Set.Icc a b) :
      HasDerivAt (fun s => star (v s) ⬝ᵥ (gMat (h s) x *ᵥ v s)) 0 t :=
    moving_metric_quadratic_hasDerivAt_zero (fun s => gMat (h s) x) v
      (ricci (h t) x) t
      (Alignment.Y03Proof.hMat_posDef (h t) x (chartPt x x)
        (mem_extChartAt_target (I := ComplexModel n) x))
      (localizedFlow_ricci_isHermitian hflow x (ha.trans_le ht.1))
      (fun i j => localizedFlow_gMat_hasDerivAt hflow x (ha.trans_le ht.1) i j)
      (hframe t ht)
  have hb := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun t ht => (hd t ht).hasDerivWithinAt)
    (fun t _ => show ‖(0 : ℂ)‖ ≤ (0 : ℝ) by simp)
    b (show b ∈ Set.Icc a b from ⟨hab, le_rfl⟩)
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm (by simpa only [zero_mul] using hb)
    (norm_nonneg _)))

theorem movingFrame_solution_vector_hasDerivAt
    (x : Pt X) (W : ℝ → (Fin n → ℂ) →L[ℝ] (Fin n → ℂ)) (u : Fin n → ℂ) (t : ℝ)
    (hW : HasDerivAt W ((movingFrameCoefficient h x t).comp (W t)) t) :
    ∀ i, HasDerivAt (fun s => W s u i) ((movingFrameMatrix h x t *ᵥ W t u) i) t := by
  have hd := hW.clm_apply (hasDerivAt_const t u)
  intro i
  simpa only [ContinuousLinearMap.comp_apply, map_zero, add_zero,
    movingFrameCoefficient, matrixRealCLM_apply] using (hasDerivAt_pi.mp hd i)

theorem localizedFlow_movingFrame_endpoint_injective
    (hflow : LocalizedFlow X o h U P ρ) (x : Pt X)
    (W : ℝ → (Fin n → ℂ) →L[ℝ] (Fin n → ℂ)) (a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (hinit : W a = ContinuousLinearMap.id ℝ (Fin n → ℂ))
    (hW : ∀ t ∈ Set.Icc a b, HasDerivAt W ((movingFrameCoefficient h x t).comp (W t)) t) :
    Function.Injective (W b) := by
  intro u v heq
  by_contra hne
  let q := u - v
  have hnorm := localizedFlow_moving_metric_norm_eq hflow x (fun s => W s q) a b ha hab
    (fun t ht => movingFrame_solution_vector_hasDerivAt x W q t (hW t ht))
  have hz : W b q = 0 := by simp only [q, map_sub, heq, sub_self]
  have hi : W a q = q := by rw [hinit]; rfl
  rw [hz, hi] at hnorm
  have hpos := (Alignment.Y03Proof.hMat_posDef (h a) x (chartPt x x)
    (mem_extChartAt_target (I := ComplexModel n) x)).dotProduct_mulVec_pos
      (show q ≠ 0 from sub_ne_zero.mpr hne)
  apply hpos.ne'
  simpa only [star_zero, Matrix.mulVec_zero, dotProduct_zero, gMat] using hnorm.symm

theorem localizedFlow_movingFrame_endpoint_surjective
    (hflow : LocalizedFlow X o h U P ρ) (x : Pt X)
    (W : ℝ → (Fin n → ℂ) →L[ℝ] (Fin n → ℂ)) (a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (hinit : W a = ContinuousLinearMap.id ℝ (Fin n → ℂ))
    (hW : ∀ t ∈ Set.Icc a b, HasDerivAt W ((movingFrameCoefficient h x t).comp (W t)) t) :
    Function.Surjective (W b) :=
  LinearMap.surjective_of_injective (f := (W b).toLinearMap)
    (localizedFlow_movingFrame_endpoint_injective hflow x W a b ha hab hinit hW)

end Yau.NodeProofs.C01Aux
