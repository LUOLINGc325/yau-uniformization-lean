import Yau.LeafProofs.L05ViscosityPrimitives

noncomputable section

open Filter MeasureTheory
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius MatrixOrder

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic

theorem productVolume_eq_restrict {n : ℕ} (O : Set (Space n)) (I : Set ℝ) :
    productVolume O I = volume.restrict (O ×ˢ I) := by
  simp only [productVolume,Measure.prod_restrict,Measure.volume_eq_prod]

theorem posSemidef_trace_mul_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι ℝ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ Matrix.trace (A*B) := by
  have hsq : CFC.sqrt B * CFC.sqrt B = B := by
    rw [← sq,CFC.sq_sqrt B hB.nonneg]
  have hstar : (CFC.sqrt B).conjTranspose = CFC.sqrt B :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg B)).isHermitian.eq
  have hh := (hA.conjTranspose_mul_mul_same (CFC.sqrt B)).trace_nonneg
  rw [hstar,Matrix.trace_mul_cycle,hsq,Matrix.trace_mul_comm] at hh
  exact hh

theorem tracePair_of_nonpos_le {n : ℕ} {ell L : ℝ} {A H : Sym n}
    (hA : A ∈ slopeSet n ell L) (hH : (-(H : Mat n)).PosSemidef) :
    tracePair A H ≤ ell*Matrix.trace (H : Mat n) := by
  have hh := posSemidef_trace_mul_nonneg hA.1 hH
  simp only [Matrix.sub_mul,Matrix.mul_neg,Matrix.smul_mul,Matrix.one_mul,
    Matrix.trace_sub,Matrix.trace_neg,Matrix.trace_smul,smul_eq_mul] at hh
  unfold tracePair
  linarith

theorem pucciPlus_of_nonpos {n : ℕ} {ell L : ℝ} (hell : 0 ≤ ell) (hL : ell ≤ L)
    (H : Sym n) (hH : (-(H : Mat n)).PosSemidef) :
    pucciPlus ell L H = ell*Matrix.trace (H : Mat n) := by
  apply le_antisymm
  · exact pucciPlus_le hL H (fun A hA => tracePair_of_nonpos_le hA hH)
  · let A : Sym n := ⟨ell • (1 : Mat n),
      IsSelfAdjoint.smul (IsSelfAdjoint.all _) (IsSelfAdjoint.one _)⟩
    have hA : A ∈ slopeSet n ell L := by
      constructor
      · change (ell • (1 : Mat n)-ell • (1 : Mat n)).PosSemidef
        simpa only [sub_self] using (Matrix.PosSemidef.zero : (0 : Mat n).PosSemidef)
      · change (L • (1 : Mat n)-ell • (1 : Mat n)).PosSemidef
        rw [← sub_smul]
        exact Matrix.PosSemidef.one.smul (sub_nonneg.mpr hL)
    simpa only [tracePair,A,Matrix.smul_mul,Matrix.one_mul,Matrix.trace_smul,smul_eq_mul]
      using tracePair_le_pucciPlus hell hA H

theorem tracePair_sub {n : ℕ} (A H K : Sym n) :
    tracePair A H-tracePair A K = tracePair A (H-K) := by
  simp only [tracePair,AddSubgroup.coe_sub,Matrix.mul_sub,Matrix.trace_sub]

theorem tracePair_sub_abs_le {n : ℕ} {ell L : ℝ} (hell : 0 ≤ ell)
    {A : Sym n} (hA : A ∈ slopeSet n ell L) (H K : Sym n) :
    |tracePair A H-tracePair A K| ≤
      (Real.sqrt (Fintype.card (RIdx n))*((2*n)*L))*‖H-K‖ := by
  rw [tracePair_sub]
  have hh := abs_trace_mul_le (A : Mat n) ((H-K : Sym n) : Mat n)
  exact hh.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (slopeSet_norm_le hell hA) (Real.sqrt_nonneg _)) (norm_nonneg _))

theorem pucciPlus_sub_le {n : ℕ} {ell L : ℝ} (hell : 0 ≤ ell) (hL : ell ≤ L)
    (H K : Sym n) : pucciPlus ell L H-pucciPlus ell L K ≤
      (Real.sqrt (Fintype.card (RIdx n))*((2*n)*L))*‖H-K‖ := by
  have hh : pucciPlus ell L H ≤ pucciPlus ell L K+
      (Real.sqrt (Fintype.card (RIdx n))*((2*n)*L))*‖H-K‖ := by
    apply pucciPlus_le hL
    intro A hA
    have hp := tracePair_le_pucciPlus hell hA K
    have hd := (le_abs_self (tracePair A H-tracePair A K)).trans
      (tracePair_sub_abs_le hell hA H K)
    linarith
  linarith

theorem pucciPlus_lipschitz {n : ℕ} {ell L : ℝ} (hell : 0 ≤ ell) (hL : ell ≤ L) :
    LipschitzWith ⟨Real.sqrt (Fintype.card (RIdx n))*((2*n)*L),
      mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg (by positivity) (hell.trans hL))⟩
      (pucciPlus (n := n) ell L) := by
  apply LipschitzWith.of_dist_le_mul
  intro H K
  change |pucciPlus ell L H-pucciPlus ell L K| ≤
    (Real.sqrt (Fintype.card (RIdx n))*((2*n)*L))*‖H-K‖
  apply abs_le.mpr
  constructor
  · have hh := pucciPlus_sub_le hell hL K H
    rw [norm_sub_rev] at hh
    linarith
  · exact pucciPlus_sub_le hell hL H K

theorem pucciPlus_continuous {n : ℕ} {ell L : ℝ} (hell : 0 ≤ ell) (hL : ell ≤ L) :
    Continuous (pucciPlus (n := n) ell L) := (pucciPlus_lipschitz hell hL).continuous

/-- A non-optimal contact determinant estimate suffices for ABP. -/
theorem contact_determinant_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    {B : Matrix ι ι ℝ} (hB : B.PosSemidef) {a k G : ℝ}
    (ha : 0 ≤ a) (hk : 0 < k) (hG : a+k*Matrix.trace B ≤ G) :
    a*B.det ≤ (k⁻¹)^Fintype.card ι*(max G 0)^(Fintype.card ι+1) := by
  have hG0 : 0 ≤ G := (add_nonneg ha (mul_nonneg hk.le hB.trace_nonneg)).trans hG
  have haG : a ≤ max G 0 := (by nlinarith [hB.trace_nonneg] : a ≤ G).trans (le_max_left _ _)
  have he (i : ι) : hB.isHermitian.eigenvalues i ≤ max G 0/k := by
    have hs : hB.isHermitian.eigenvalues i ≤ Matrix.trace B := by
      rw [hB.isHermitian.trace_eq_sum_eigenvalues]
      exact Finset.single_le_sum (fun j _ => hB.eigenvalues_nonneg j) (Finset.mem_univ i)
    apply (le_div_iff₀ hk).2
    have hh := mul_le_mul_of_nonneg_left hs hk.le
    nlinarith [le_max_left G 0]
  have hdet : B.det ≤ (max G 0/k)^Fintype.card ι := by
    rw [hB.isHermitian.det_eq_prod_eigenvalues]
    calc
      _ ≤ ∏ _i : ι, max G 0/k := Finset.prod_le_prod₀
        (fun i _ => hB.eigenvalues_nonneg i) (fun i _ => he i)
      _ = _ := by simp only [Finset.prod_const,Finset.card_univ]
  calc
    _ ≤ max G 0*(max G 0/k)^Fintype.card ι :=
      mul_le_mul haG hdet hB.det_nonneg (le_max_right _ _)
    _ = _ := by simp only [div_eq_mul_inv,mul_pow,pow_succ]; ring

theorem abp_root_of_power {p : ℕ} (hp : 0 < p) {m A integralValue : ℝ}
    (hm : 0 ≤ m) (hA : 0 ≤ A) (hI : 0 ≤ integralValue) (h : m^p ≤ A*integralValue) :
    m ≤ (1+A)*integralValue^(1/(p : ℝ)) := by
  have hAp : A ≤ (1+A)^p := by
    obtain ⟨q,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp.ne'
    rw [pow_succ]
    have hh : 1 ≤ (1+A)^q := one_le_pow₀ (by linarith : 1 ≤ 1+A)
    nlinarith
  have hroot : (integralValue^(1/(p : ℝ)))^p = integralValue := by
    simpa only [one_div] using Real.rpow_inv_natCast_pow hI hp.ne'
  have hpow : m^p ≤ ((1+A)*integralValue^(1/(p : ℝ)))^p := by
    rw [mul_pow,hroot]
    exact h.trans (mul_le_mul_of_nonneg_right hAp hI)
  exact (pow_le_pow_iff_left₀ hm
    (mul_nonneg (by linarith : 0 ≤ 1+A) (Real.rpow_nonneg hI _)) hp.ne').mp hpow

/-- Row elimination for the actual contact-map block matrix, requiring no
inverse of the spatial Hessian. -/
theorem contact_block_det {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℝ) (c : Matrix ι Unit ℝ) (x : Matrix Unit ι ℝ) (a : ℝ) :
    (Matrix.fromBlocks H c (-(x*H)) (a • (1 : Matrix Unit Unit ℝ)-x*c)).det = H.det*a := by
  have hf : Matrix.fromBlocks H c (-(x*H)) (a • (1 : Matrix Unit Unit ℝ)-x*c) =
      Matrix.fromBlocks (1 : Matrix ι ι ℝ) 0 (-x) 1 *
        Matrix.fromBlocks H c 0 (a • (1 : Matrix Unit Unit ℝ)) := by
    rw [Matrix.fromBlocks_multiply]
    simp only [Matrix.one_mul,Matrix.zero_mul,Matrix.mul_zero,add_zero,
      Matrix.neg_mul,sub_eq_add_neg,add_comm]
  rw [hf,Matrix.det_mul,Matrix.det_fromBlocks_zero₁₂,Matrix.det_fromBlocks_zero₂₁]
  simp

end Yau.LeafProofs.L05Aux
