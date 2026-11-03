import Yau.Blueprint.Alignment

/-! The actual Kähler–Ricci equation in logarithmic time and a fixed frame. -/

open scoped Topology Matrix

noncomputable section

namespace Yau.Blueprint.Alignment.Y03Proof

open Yau

variable {n : ℕ} {M : ComplexManifold n}

theorem kahlerRicciFlow_gMat_hasDerivAt {g : HermitianField M} {h : ℝ → HermitianField M}
    (hflow : IsKahlerRicciFlow g h) (x : M.Carrier) {t : ℝ} (ht : 0 < t) (i j : Fin n) :
    HasDerivAt (fun s => gMat (h s) x i j) (-(ricci (h t) x i j)) t :=
  (hflow.2.2.2 x t ht.le i j).hasDerivAt (Ici_mem_nhds ht)

theorem logarithmic_gMat_hasDerivAt {g : HermitianField M} {h : ℝ → HermitianField M}
    (hflow : IsKahlerRicciFlow g h) (x : M.Carrier) {t : ℝ} (ht : 0 < t)
    (τ : ℝ) (i j : Fin n) :
    HasDerivAt (fun s => gMat (h (t * Real.exp s)) x i j)
      (-((t * Real.exp τ : ℝ) : ℂ) * ricci (h (t * Real.exp τ)) x i j) τ := by
  have hs : 0 < t * Real.exp τ := mul_pos ht (Real.exp_pos τ)
  have htime : HasDerivAt (fun s => t * Real.exp s) (t * Real.exp τ) τ :=
    (Real.hasDerivAt_exp τ).const_mul t
  convert (kahlerRicciFlow_gMat_hasDerivAt hflow x hs i j).scomp τ htime using 1
  · rfl
  · simp only [Complex.real_smul]
    ring

theorem fixed_frame_logarithmic_metric_hasDerivAt {g : HermitianField M}
    {h : ℝ → HermitianField M} (hflow : IsKahlerRicciFlow g h) (x : M.Carrier)
    (P : Herm n) {t : ℝ} (ht : 0 < t) (τ : ℝ) (i j : Fin n) :
    HasDerivAt (fun s => (P.conjTranspose * gMat (h (t * Real.exp s)) x * P) i j)
      (-(P.conjTranspose * (((t * Real.exp τ : ℝ) : ℂ) • ricci (h (t * Real.exp τ)) x) * P) i j) τ := by
  have hentry := logarithmic_gMat_hasDerivAt hflow x ht τ
  have hd := HasDerivAt.sum (u := Finset.univ) (fun l _ =>
    (HasDerivAt.sum (u := Finset.univ) (fun a _ =>
      (hentry a l).const_mul (P.conjTranspose i a))).mul_const (P l j))
  convert hd using 1
  · funext s
    simp only [Matrix.mul_apply, Finset.sum_apply]
  · simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, mul_neg, neg_mul,
      Finset.sum_neg_distrib]

end Yau.Blueprint.Alignment.Y03Proof
