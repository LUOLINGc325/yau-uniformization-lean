import Yau.Proofs.F03LinearTensorTransport

/-! All tensor orders of an affine restriction, including actual spatial slices. -/
noncomputable section
open Filter Set
open scoped Topology ContDiff
namespace Yau.Proofs.F03Aux
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000

theorem iteratedFDeriv_comp_affine_of_isOpen
    (D : Set F) (hD : IsOpen D) (f : F → ℝ) (hf : ContDiffOn ℝ ∞ f D)
    (L : E →L[ℝ] F) (c : F) (x : E) (hx : L x+c ∈ D) (m : ℕ) :
    iteratedFDeriv ℝ m (fun y => f (L y+c)) x=
      (iteratedFDeriv ℝ m f (L x+c)).compContinuousLinearMap (fun _ => L) := by
  let g : F → ℝ := fun y => f (y+c)
  let S : Set F := {y | y+c ∈ D}
  have hS : IsOpen S := hD.preimage (continuous_id.add continuous_const)
  have hPre : IsOpen (L ⁻¹' S) := hS.preimage L.continuous
  have hg : ContDiffOn ℝ ∞ g S := hf.comp (contDiff_id.add contDiff_const).contDiffOn (fun _ hy => hy)
  have h := L.iteratedFDerivWithin_comp_right hg hS.uniqueDiffOn hPre.uniqueDiffOn hx (i := m) (by simp)
  rw [iteratedFDerivWithin_of_isOpen m hPre hx,iteratedFDerivWithin_of_isOpen m hS hx] at h
  simpa only [g,Function.comp_def,iteratedFDeriv_comp_add_right] using h

theorem norm_iteratedFDeriv_comp_affine_le
    (D : Set F) (hD : IsOpen D) (f : F → ℝ) (hf : ContDiffOn ℝ ∞ f D)
    (L : E →L[ℝ] F) (c : F) (x : E) (hx : L x+c ∈ D) (m : ℕ) :
    ‖iteratedFDeriv ℝ m (fun y => f (L y+c)) x‖ ≤
      ‖iteratedFDeriv ℝ m f (L x+c)‖*‖L‖^m := by
  rw [iteratedFDeriv_comp_affine_of_isOpen D hD f hf L c x hx m]
  simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] using
    (iteratedFDeriv ℝ m f (L x+c)).norm_compContinuousLinearMap_le (fun _ : Fin m => L)

theorem norm_iteratedFDeriv_spatial_slice_le
    (D : Set (E × ℝ)) (hD : IsOpen D) (f : E × ℝ → ℝ) (hf : ContDiffOn ℝ ∞ f D)
    (x : E) (t : ℝ) (hp : (x,t) ∈ D) (m : ℕ) :
    ‖iteratedFDeriv ℝ m (fun y => f (y,t)) x‖ ≤ ‖iteratedFDeriv ℝ m f (x,t)‖ := by
  let L : E →L[ℝ] E × ℝ := (ContinuousLinearMap.id ℝ E).prod 0
  have hL : ‖L‖ ≤ 1 := by
    apply L.opNorm_le_bound (by norm_num)
    intro y
    simp only [L,ContinuousLinearMap.prod_apply,ContinuousLinearMap.id_apply,
      ContinuousLinearMap.zero_apply,Prod.norm_def,norm_zero,max_eq_left (norm_nonneg _),one_mul]
    exact le_rfl
  have h := norm_iteratedFDeriv_comp_affine_le D hD f hf L (0,t) x (by simpa [L] using hp) m
  have hPow : ‖L‖^m ≤ 1 := by simpa using pow_le_pow_left₀ (norm_nonneg _) hL m
  have hBound := h.trans (mul_le_mul_of_nonneg_left hPow (norm_nonneg _))
  simpa [L] using hBound

end Yau.Proofs.F03Aux
