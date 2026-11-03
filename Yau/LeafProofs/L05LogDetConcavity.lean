import Yau.LeafProofs.L05LogDetModulus

noncomputable section

open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic

local instance l05LogDetConcavitySymContinuousSMul (n : ℕ) : ContinuousSMul ℝ (Sym n) :=
  (show Topology.IsInducing (fun A : Sym n => (A : Mat n)) from ⟨rfl⟩).continuousSMul
    (f := fun c : ℝ => c) continuous_id (by intros; rfl)

theorem trace_inverse_quadratic_nonneg {n : ℕ} {A B : Mat n}
    (hA : A.PosSemidef) (hB : B.PosSemidef) (V : Sym n) :
    0 ≤ Matrix.trace (A*(V : Mat n)*B*(V : Mat n)) := by
  have hVs : (V : Mat n).conjTranspose=(V : Mat n) :=
    (Matrix.isHermitian_iff_isSelfAdjoint.mpr V.property).eq
  have hh := posSemidef_trace_mul_nonneg hA (hB.conjTranspose_mul_mul_same (V : Mat n))
  simpa only [hVs,Matrix.mul_assoc] using hh

theorem logDetReal_segment_hasDerivAt {n : ℕ} {A V : Sym n} {t : ℝ}
    (ht : A+t • V ∈ logDetDomain n) :
    HasDerivAt (fun s : ℝ => logDetReal (A+s • V))
      ((1/2:ℝ)*Matrix.trace (((A+t • V : Sym n) : Mat n)⁻¹*(V : Mat n))) t := by
  have hp : HasDerivAt (fun s : ℝ => A+s • V) V t := by
    convert! (hasDerivAt_const t A).add ((hasDerivAt_id t).smul_const V) using 1 <;>
      simp only [one_smul,zero_add]
  have hd := ((logDetReal_contDiffOn n).contDiffAt ((logDetDomain_isOpen n).mem_nhds ht)).differentiableAt (by simp)
  have hh := hd.hasFDerivAt.comp_hasDerivAt t hp
  convert! hh using 1
  convert! (logDetReal_fderiv ht V).symm using 1

set_option maxHeartbeats 1200000 in
theorem logDetReal_concaveOn_slopeSet {n : ℕ} {ell L : ℝ}
    (hell : 0 < ell) (hL : ell ≤ L) : ConcaveOn ℝ (slopeSet n ell L) (@logDetReal n) := by
  refine ⟨slopeSet_convex n ell L,?_⟩
  intro A hA B hB a b ha hb hab
  let V := B-A
  let X := fun t : ℝ => A+t • V
  let f := fun t : ℝ => logDetReal (X t)
  have hX (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) : X t ∈ slopeSet n ell L := by
    have he : X t=(1-t) • A+t • B := by
      dsimp only [X,V]
      rw [sub_smul,one_smul,smul_sub]
      abel
    rw [he]
    exact slopeSet_convex n ell L hA hB (sub_nonneg.mpr ht.2) ht.1 (by ring)
  have hf (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) :
      HasDerivAt f ((1/2:ℝ)*Matrix.trace ((X t : Mat n)⁻¹*(V : Mat n))) t :=
    logDetReal_segment_hasDerivAt (slopeSet_subset_logDetDomain hell (hX t ht))
  have hanti : AntitoneOn (deriv f) (interior (Set.Icc (0:ℝ) 1)) := by
    intro s hs t ht hst
    have hsI := interior_subset hs
    have htI := interior_subset ht
    rw [(hf s hsI).deriv,(hf t htI).deriv]
    have hXs := slopeSet_posDef hell (hX s hsI)
    have hXt := slopeSet_posDef hell (hX t htI)
    have hpos := trace_inverse_quadratic_nonneg hXs.inv.posSemidef hXt.inv.posSemidef V
    have hdiff : (X t : Mat n)-(X s : Mat n)=(t-s) • (V : Mat n) := by
      change ((A : Mat n)+t • (V : Mat n))-((A : Mat n)+s • (V : Mat n))=_
      rw [sub_smul]
      abel
    have hinv := inverse_sub_identity hXs.det_pos.ne' hXt.det_pos.ne'
    have htrace : Matrix.trace ((X s : Mat n)⁻¹*(V : Mat n))-
        Matrix.trace ((X t : Mat n)⁻¹*(V : Mat n))=
        (t-s)*Matrix.trace ((X s : Mat n)⁻¹*(V : Mat n)*(X t : Mat n)⁻¹*(V : Mat n)) := by
      rw [← Matrix.trace_sub,← Matrix.sub_mul,hinv,hdiff,Matrix.mul_smul,
        Matrix.smul_mul,Matrix.smul_mul,Matrix.trace_smul,smul_eq_mul]
    nlinarith only [htrace,mul_nonneg (sub_nonneg.mpr hst) hpos]
  have hc : ConcaveOn ℝ (Set.Icc (0:ℝ) 1) f := hanti.concaveOn_of_deriv (convex_Icc 0 1)
    (fun t ht => (hf t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hf t (interior_subset ht)).differentiableAt.differentiableWithinAt)
  have hm := hc.2 (show (0:ℝ) ∈ Set.Icc (0:ℝ) 1 by norm_num)
    (show (1:ℝ) ∈ Set.Icc (0:ℝ) 1 by norm_num) ha hb hab
  have h0 : X 0=A := by simp only [X,zero_smul,add_zero]
  have h1 : X 1=B := by dsimp only [X,V]; rw [one_smul]; abel
  have he : a • A+b • B=X b := by
    dsimp only [X,V]
    have ha' : a=1-b := by linarith
    rw [ha',sub_smul,one_smul,smul_sub]
    abel
  change a*logDetReal A+b*logDetReal B ≤ logDetReal (a • A+b • B)
  simpa only [smul_eq_mul,mul_zero,mul_one,zero_add,f,h0,h1,he] using hm

end Yau.LeafProofs.L05Aux
