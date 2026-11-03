import Yau.LeafProofs.L05DualEllipticity

noncomputable section

open Filter
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic Yau.ParabolicCandidates

local instance l05ChuSupportingSymContinuousSMul (n : ℕ) : ContinuousSMul ℝ (Sym n) :=
  (show Topology.IsInducing (fun A : Sym n => (A : Mat n)) from ⟨rfl⟩).continuousSMul
    (f := fun c : ℝ => c) continuous_id (by intros; rfl)

theorem chu_matrix_contDiffOn {n : ℕ} {E U : Set (Sym n)} {F : Sym n → Point n → ℝ}
    {ell L K beta : ℝ} (hF : ChuH1 E U F ell L K beta)
    {p : Point n} (hp : p ∈ backward 1) : ContDiffOn ℝ 1 (fun A => F A p) U :=
  hF.2.2.1.comp (contDiff_id.prodMk contDiff_const).contDiffOn (fun _ hA => ⟨hA,hp⟩)

theorem chu_matrix_continuousOn {n : ℕ} {E U : Set (Sym n)} {F : Sym n → Point n → ℝ}
    {ell L K beta : ℝ} (hF : ChuH1 E U F ell L K beta)
    {p : Point n} (hp : p ∈ backward 1) : ContinuousOn (fun A => F A p) E :=
  (chu_matrix_contDiffOn hF hp).continuousOn.mono hF.2.1

theorem midpoint_supports_derivative {g : ℝ → ℝ} {d : ℝ} (hg : HasDerivAt g d 0)
    (hm : ∀ t ∈ Set.Icc (0:ℝ) 1, (g 0+g t)/2 ≤ g (t/2)) : g 1 ≤ g 0+d := by
  let a := fun k : ℕ => (1/2:ℝ)^k
  have ha (k : ℕ) : 0 < a k := pow_pos (by norm_num) k
  have ha1 (k : ℕ) : a k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hval (k : ℕ) : g 0+a k*(g 1-g 0) ≤ g (a k) := by
    induction k with
    | zero => simp only [a,pow_zero,one_mul,add_sub_cancel]; exact le_rfl
    | succ k ih =>
      have hr := hm (a k) ⟨(ha k).le,ha1 k⟩
      have he : a (k+1)=a k/2 := by dsimp only [a]; rw [pow_succ]; ring
      rw [he]
      nlinarith only [ih,hr]
  have hat : Tendsto a atTop (𝓝 (0:ℝ)) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hatp : Tendsto a atTop (𝓝[>] (0:ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hat,Eventually.of_forall ha⟩
  have hlim : Tendsto (fun k => (a k)⁻¹*(g (a k)-g 0)) atTop (𝓝 d) := by
    convert! hg.tendsto_slope_zero_right.comp hatp using 1 <;>
      simp only [zero_add,smul_eq_mul] <;> rfl
  have hlo (k : ℕ) : g 1-g 0 ≤ (a k)⁻¹*(g (a k)-g 0) := by
    have hh : g 1-g 0 ≤ (g (a k)-g 0)/a k :=
      (le_div_iff₀ (ha k)).mpr (by nlinarith only [hval k])
    simpa only [div_eq_mul_inv,mul_comm] using hh
  have hh := ge_of_tendsto hlim (Eventually.of_forall hlo)
  linarith only [hh]

set_option maxHeartbeats 1200000 in
theorem chu_supporting_plane {n : ℕ} {E U : Set (Sym n)} {F : Sym n → Point n → ℝ}
    {ell L K beta : ℝ} (hE : Convex ℝ E) (hF : ChuH1 E U F ell L K beta)
    {M N : Sym n} (hM : M ∈ E) (hN : N ∈ E) {p : Point n} (hp : p ∈ backward 1) :
    F N p ≤ F M p+tracePair (chuSlope F M p) (N-M) := by
  let V := N-M
  let g := fun t : ℝ => F (M+t • V) p
  have hc : ContDiffOn ℝ 1 (fun A => F A p) U := hF.2.2.1.comp
    (contDiff_id.prodMk contDiff_const).contDiffOn (fun A hA => ⟨hA,hp⟩)
  have hd := (hc.contDiffAt (hF.1.mem_nhds (hF.2.1 hM))).differentiableAt (by norm_num)
  have hpath : HasDerivAt (fun t : ℝ => M+t • V) V 0 := by
    convert! (hasDerivAt_const (0:ℝ) M).add ((hasDerivAt_id (0:ℝ)).smul_const V) using 1 <;>
      simp only [one_smul,zero_add]
  have hd0 : DifferentiableAt ℝ (fun A => F A p) (M+(0:ℝ) • V) := by
    convert! hd using 1 <;> simp only [zero_smul,add_zero]
  have hg : HasDerivAt g (fderiv ℝ (fun A => F A p) M V) 0 := by
    convert! hd0.hasFDerivAt.comp_hasDerivAt (0:ℝ) hpath using 1 <;>
      simp only [zero_smul,add_zero] <;> rfl
  have hm : ∀ t ∈ Set.Icc (0:ℝ) 1, (g 0+g t)/2 ≤ g (t/2) := by
    intro t ht
    have hXt : M+t • V ∈ E := by
      have he : M+t • V=(1-t) • M+t • N := by
        dsimp only [V]
        rw [sub_smul,one_smul,smul_sub]
        abel
      rw [he]
      exact hE hM hN (sub_nonneg.mpr ht.2) ht.1 (by ring)
    have hh := hF.2.2.2.2.1 M hM (M+t • V) hXt p hp
    have he : (1/2:ℝ) • (M+(M+t • V))=M+(t/2) • V := by
      rw [smul_add,smul_add,smul_smul,← add_assoc,← add_smul]
      norm_num
      congr 1
      ring
    dsimp only [g]
    rw [zero_smul,add_zero]
    exact hh.trans_eq (congrArg (fun A => F A p) he)
  have hh := midpoint_supports_derivative hg hm
  have he1 : M+(1:ℝ) • V=N := by dsimp only [V]; rw [one_smul]; abel
  dsimp only [g] at hh
  rw [he1,zero_smul,add_zero,chuSlope_apply] at hh
  exact hh

end Yau.LeafProofs.L05Aux
