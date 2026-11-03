import Yau.LeafProofs.L05ChuReduction

noncomputable section

open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic Yau.ParabolicCandidates

local instance l05ChuLinearizationSymContinuousSMul (n : ℕ) : ContinuousSMul ℝ (Sym n) :=
  (show Topology.IsInducing (fun A : Sym n => (A : Mat n)) from ⟨rfl⟩).continuousSMul
    (f := fun c : ℝ => c) continuous_id (by intros; rfl)

theorem symLinearFunctional_bound_of_unit {n : ℕ} (l : Sym n →ₗ[ℝ] ℝ) {c : ℝ}
    (hc : ∀ V : Sym n, ‖V‖ ≤ 1 → |l V| ≤ c) (V : Sym n) : |l V| ≤ c*‖V‖ := by
  by_cases hV : V=0
  · subst V
    simp only [map_zero,abs_zero,norm_zero,mul_zero,le_refl]
  have hn : 0 < ‖V‖ := norm_pos_iff.mpr hV
  have hunit : ‖(‖V‖⁻¹:ℝ) • V‖=1 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hn),inv_mul_cancel₀ hn.ne']
  have hh := hc ((‖V‖⁻¹:ℝ) • V) hunit.le
  rw [map_smul,smul_eq_mul,abs_mul,abs_of_pos (inv_pos.mpr hn)] at hh
  have hm := mul_le_mul_of_nonneg_left hh hn.le
  have he : ‖V‖*(‖V‖⁻¹*|l V|)=|l V| := by rw [← mul_assoc,mul_inv_cancel₀ hn.ne',one_mul]
  rw [he] at hm
  exact hm.trans_eq (mul_comm _ _)

theorem chuDerivativeModulus_homogeneous {n : ℕ} {E : Set (Sym n)}
    {F : Sym n → Point n → ℝ} {omega : ℝ → ℝ} (hDF : ChuDerivativeModulus E F omega)
    {A B : Sym n} (hA : A ∈ E) (hB : B ∈ E) {p q : Point n}
    (hp : p ∈ backward 1) (hq : q ∈ backward 1) (V : Sym n) :
    |fderiv ℝ (fun N => F N p) A V-fderiv ℝ (fun N => F N q) B V| ≤
      omega (‖A-B‖+parabolicDistance p q)*‖V‖ := by
  let l := (fderiv ℝ (fun N => F N p) A-fderiv ℝ (fun N => F N q) B).toLinearMap
  have hh := symLinearFunctional_bound_of_unit l
    (fun W hW => hDF A hA B hB p hp q hq W hW) V
  exact hh

set_option maxHeartbeats 1400000 in
theorem chu_linearization_error {n : ℕ} {E U : Set (Sym n)} (hE : Convex ℝ E)
    {F : Sym n → Point n → ℝ} {ell L K beta : ℝ} (hF : ChuH1 E U F ell L K beta)
    {omega : ℝ → ℝ} (hm : Modulus omega) (hDF : ChuDerivativeModulus E F omega)
    {A B A0 : Sym n} (hA : A ∈ E) (hB : B ∈ E) (hA0 : A0 ∈ E)
    {p p0 : Point n} (hp : p ∈ backward 1) (hp0 : p0 ∈ backward 1)
    {delta : ℝ} (hd : 0 ≤ delta) (hAd : ‖A-A0‖ ≤ delta) (hBd : ‖B-A0‖ ≤ delta) :
    |F A p-F B p-fderiv ℝ (fun N => F N p0) A0 (A-B)| ≤
      omega (delta+parabolicDistance p p0)*‖A-B‖ := by
  let C := E ∩ Metric.closedBall A0 delta
  let l := fderiv ℝ (fun N => F N p0) A0
  have hCV : Convex ℝ C := hE.inter (convex_closedBall A0 delta)
  have hAC : A ∈ C := ⟨hA,Metric.mem_closedBall.mpr (by simpa only [dist_eq_norm] using hAd)⟩
  have hBC : B ∈ C := ⟨hB,Metric.mem_closedBall.mpr (by simpa only [dist_eq_norm] using hBd)⟩
  have hDist : 0 ≤ parabolicDistance p p0 := add_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)
  have hFd (N : Sym n) (hN : N ∈ C) : DifferentiableAt ℝ (fun M => F M p) N := by
    convert! ((chu_matrix_contDiffOn hF hp).contDiffAt (hF.1.mem_nhds (hF.2.1 hN.1))).differentiableAt (by norm_num) using 1
  let V := A-B
  let X := fun t : ℝ => B+t • V
  let phi := fun t : ℝ => F (X t) p-l (X t)
  let phiD := fun t : ℝ => fderiv ℝ (fun M => F M p) (X t) V-l V
  have hX (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) : X t ∈ C := by
    have he : X t=(1-t) • B+t • A := by
      dsimp only [X,V]
      rw [sub_smul,one_smul,smul_sub]
      abel
    rw [he]
    exact hCV hBC hAC (sub_nonneg.mpr ht.2) ht.1 (by ring)
  have hder (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) : HasDerivAt phi (phiD t) t := by
    have hxder : HasDerivAt X V t := by
      convert! (hasDerivAt_const t B).add ((hasDerivAt_id t).smul_const V) using 1 <;>
        simp only [one_smul,zero_add]
    have hfder := (hFd (X t) (hX t ht)).hasFDerivAt.comp_hasDerivAt t hxder
    have hlder := l.hasFDerivAt.comp_hasDerivAt t hxder
    convert! hfder.sub hlder using 1
  have hbound (t : ℝ) (ht : t ∈ Set.Ico (0:ℝ) 1) :
      ‖phiD t‖ ≤ omega (delta+parabolicDistance p p0)*‖V‖ := by
    have hN := hX t ⟨ht.1,ht.2.le⟩
    have hh := chuDerivativeModulus_homogeneous hDF hN.1 hA0 hp hp0 V
    have hNd : ‖X t-A0‖ ≤ delta := by simpa only [dist_eq_norm] using Metric.mem_closedBall.mp hN.2
    have hmono := hm.2.2.1 (show ‖X t-A0‖+parabolicDistance p p0 ∈ Set.Ici 0 from add_nonneg (norm_nonneg _) hDist)
      (show delta+parabolicDistance p p0 ∈ Set.Ici 0 from add_nonneg hd hDist) (add_le_add hNd le_rfl)
    change |fderiv ℝ (fun M => F M p) (X t) V-l V| ≤ _
    exact hh.trans (mul_le_mul_of_nonneg_right hmono (norm_nonneg _))
  have hh := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (fun t ht => (hder t ht).hasDerivWithinAt) hbound
  have hX1 : X 1=A := by dsimp only [X,V]; rw [one_smul]; abel
  have hX0 : X 0=B := by dsimp only [X]; rw [zero_smul,add_zero]
  change ‖(F (X 1) p-l (X 1))-(F (X 0) p-l (X 0))‖ ≤ _ at hh
  rw [hX1,hX0] at hh
  have he : (F A p-l A)-(F B p-l B)=F A p-F B p-l (A-B) := by rw [map_sub]; ring
  rw [he,Real.norm_eq_abs] at hh
  exact hh

theorem chu_linearization_spaceTime_error {n : ℕ} {E U : Set (Sym n)} (hE : Convex ℝ E)
    {F : Sym n → Point n → ℝ} {ell L K beta : ℝ} (hF : ChuH1 E U F ell L K beta)
    {omega : ℝ → ℝ} (hm : Modulus omega) (hDF : ChuDerivativeModulus E F omega)
    {A B A0 : Sym n} (hA : A ∈ E) (hB : B ∈ E) (hA0 : A0 ∈ E)
    {p q p0 : Point n} (hp : p ∈ backward 1) (hq : q ∈ backward 1) (hp0 : p0 ∈ backward 1)
    {delta : ℝ} (hd : 0 ≤ delta) (hAd : ‖A-A0‖ ≤ delta) (hBd : ‖B-A0‖ ≤ delta) :
    |F A p-F B q-fderiv ℝ (fun N => F N p0) A0 (A-B)| ≤
      omega (delta+parabolicDistance p p0)*‖A-B‖+K*holderWeight beta p q := by
  have hl := chu_linearization_error hE hF hm hDF hA hB hA0 hp hp0 hd hAd hBd
  have ht := hF.2.2.2.2.2.1 B hB p hp q hq
  have hh := abs_add_le (F A p-F B p-fderiv ℝ (fun N => F N p0) A0 (A-B)) (F B p-F B q)
  have he : (F A p-F B p-fderiv ℝ (fun N => F N p0) A0 (A-B))+(F B p-F B q)=
      F A p-F B q-fderiv ℝ (fun N => F N p0) A0 (A-B) := by ring
  rw [he] at hh
  exact hh.trans (add_le_add hl ht)

end Yau.LeafProofs.L05Aux
