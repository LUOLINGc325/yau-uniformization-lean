import Yau.LeafProofs.L05ABPAlgebra

open Filter MeasureTheory Set Unitary
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius MatrixOrder
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

theorem jet_exists_pucci_spectral_split {n : ℕ} {ell L : ℝ}
    (hL : ell≤L) (H : Sym n) :
    ∃ P N A : Sym n,
      (P : Mat n).PosSemidef ∧ (N : Mat n).PosSemidef ∧ H=P-N ∧
      A ∈ slopeSet n ell L ∧
      tracePair A H=L*Matrix.trace (P : Mat n)-ell*Matrix.trace (N : Mat n) := by
  classical
  have hH : (H : Mat n).IsHermitian := Matrix.isHermitian_iff_isSelfAdjoint.mpr H.property
  let U := hH.eigenvectorUnitary
  let f := conjStarAlgAut ℝ (Mat n) U
  let h := hH.eigenvalues
  let p := fun i => max (h i) 0
  let m := fun i => max (-h i) 0
  let c := fun i => if 0<h i then L else ell
  have hDiag (v : Yau.RIdx n → ℝ) : IsSelfAdjoint (Matrix.diagonal v) := by
    exact Matrix.isHermitian_iff_isSelfAdjoint.mp
      (Matrix.isHermitian_diagonal_iff.mpr fun _ => IsSelfAdjoint.all _)
  have hSelf (v : Yau.RIdx n → ℝ) : IsSelfAdjoint (f (Matrix.diagonal v)) := by
    rw [isSelfAdjoint_iff,← map_star f]
    rw [(hDiag v).star_eq]
  have hPSD (v : Yau.RIdx n → ℝ) (hv : ∀ i, 0≤v i) :
      (f (Matrix.diagonal v)).PosSemidef := by
    have hd : (Matrix.diagonal v).PosSemidef := Matrix.posSemidef_diagonal_iff.mpr hv
    simpa only [f,conjStarAlgAut_apply,Matrix.star_eq_conjTranspose] using
      hd.mul_mul_conjTranspose_same (U : Mat n)
  let P : Sym n := ⟨f (Matrix.diagonal p),hSelf p⟩
  let N : Sym n := ⟨f (Matrix.diagonal m),hSelf m⟩
  let A : Sym n := ⟨f (Matrix.diagonal c),hSelf c⟩
  have hSpectral : (H : Mat n)=f (Matrix.diagonal h) := by
    simpa only [f,U,h,Function.comp_def,RCLike.ofReal_real_eq_id,id_eq] using hH.spectral_theorem
  have hSplit (i) : h i=p i-m i := by
    dsimp only [p,m]
    by_cases hi : 0≤h i
    · rw [max_eq_left hi,max_eq_right (by linarith : -h i≤0)]
      ring
    · rw [max_eq_right (le_of_not_ge hi),max_eq_left (by linarith : 0≤-h i)]
      ring
  have hPN : H=P-N := by
    apply Subtype.ext
    change (H : Mat n)=f (Matrix.diagonal p)-f (Matrix.diagonal m)
    rw [hSpectral,← map_sub,Matrix.diagonal_sub]
    congr 2
    funext i
    exact hSplit i
  have hConst (d : ℝ) : Matrix.diagonal (fun _ : Yau.RIdx n => d)=d • (1 : Mat n) := by
    ext i j
    by_cases hij : i=j <;> simp [hij]
  have hSlope : A ∈ slopeSet n ell L := by
    constructor
    · have hh := hPSD (fun i => c i-ell) (by
        intro i
        dsimp only [c]
        split_ifs <;> linarith)
      change (f (Matrix.diagonal c)-ell • (1 : Mat n)).PosSemidef
      rw [← Matrix.diagonal_sub] at hh
      simpa only [map_sub,hConst,map_smul,map_one] using hh
    · have hh := hPSD (fun i => L-c i) (by
        intro i
        dsimp only [c]
        split_ifs <;> linarith)
      change (L • (1 : Mat n)-f (Matrix.diagonal c)).PosSemidef
      rw [← Matrix.diagonal_sub] at hh
      simpa only [map_sub,hConst,map_smul,map_one] using hh
  have hTrace (D : Mat n) : Matrix.trace (f D)=Matrix.trace D := by
    dsimp only [f]
    rw [conjStarAlgAut_apply,Matrix.trace_mul_cycle,Unitary.coe_star_mul_self,Matrix.one_mul]
  refine ⟨P,N,A,hPSD p (fun i => le_max_right _ _),
    hPSD m (fun i => le_max_right _ _),hPN,hSlope,?_⟩
  change Matrix.trace (f (Matrix.diagonal c)*(H : Mat n))=
    L*Matrix.trace (f (Matrix.diagonal p))-ell*Matrix.trace (f (Matrix.diagonal m))
  rw [hSpectral,← map_mul,hTrace,hTrace,hTrace,Matrix.diagonal_mul_diagonal]
  simp only [Matrix.trace_diagonal,Finset.mul_sum,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  dsimp only [c,p,m]
  by_cases hi : 0<h i
  · rw [ite_eq_left hi,max_eq_left hi.le,max_eq_right (by linarith : -h i≤0)]
    ring
  · rw [ite_eq_right hi,max_eq_right (not_lt.mp hi),max_eq_left (by linarith : 0≤-h i)]
    ring

theorem jet_elliptic_difference_le_pucci {n : ℕ} {F : Sym n → ℝ} {ell L : ℝ}
    (hell : 0≤ell) (hL : ell≤L) (hF : globalElliptic F ell L) (X Y : Sym n) :
    F X-F Y≤pucciPlus ell L (X-Y) := by
  obtain ⟨P,N,A,hP,hN,hSplit,hA,hTrace⟩ := jet_exists_pucci_spectral_split hL (X-Y)
  let M := Y-N
  have hx : M+P=X := by
    have hs : X-Y=P-N := hSplit
    dsimp only [M]
    calc
      Y-N+P = Y+(P-N) := by abel
      _ = X := by rw [← hs]; abel
  have hy : M+N=Y := by dsimp only [M]; abel
  have hu := (hF M P hP).2
  have hl := (hF M N hN).1
  rw [hx] at hu
  rw [hy] at hl
  have hp := tracePair_le_pucciPlus hell hA (X-Y)
  rw [hTrace] at hp
  linarith

theorem jet_slope_trace_le {n : ℕ} {ell L : ℝ} {A : Sym n}
    (hA : A ∈ slopeSet n ell L) : Matrix.trace (A : Mat n)≤(2*n)*L := by
  have ht : Matrix.trace (A : Mat n)≤(Fintype.card (Yau.RIdx n) : ℝ)*L := by
    calc
      _ = ∑ i, (A : Mat n) i i := rfl
      _ ≤ ∑ _i : Yau.RIdx n, L := Finset.sum_le_sum fun i _ => by
        have hd := hA.2.diag_nonneg (i := i)
        simpa only [Matrix.sub_apply,Matrix.smul_apply,Matrix.one_apply_eq,smul_eq_mul,
          mul_one,sub_nonneg] using hd
      _ = _ := by simp
  have hc : (Fintype.card (Yau.RIdx n) : ℝ)=2*n := by simp [Yau.RIdx]; ring
  rwa [hc] at ht

theorem jet_pucci_le_of_matrix_le {n : ℕ} {ell L kappa : ℝ} {X H : Sym n}
    (hell : 0≤ell) (hL : ell≤L) (hk : 0≤kappa)
    (hmat : ((H : Mat n)+kappa • (1 : Mat n)-(X : Mat n)).PosSemidef) :
    pucciPlus ell L X≤pucciPlus ell L H+kappa*(2*n)*L := by
  apply pucciPlus_le hL
  intro A hA
  have hn := posSemidef_trace_mul_nonneg (slopeSet_posSemidef hell hA) hmat
  simp only [Matrix.mul_sub,Matrix.mul_add,Matrix.mul_smul,Matrix.mul_one,
    Matrix.trace_sub,Matrix.trace_add,Matrix.trace_smul,smul_eq_mul] at hn
  have hp := tracePair_le_pucciPlus hell hA H
  have ht := mul_le_mul_of_nonneg_left (jet_slope_trace_le hA) hk
  unfold tracePair at hp ⊢
  nlinarith only [hn,hp,ht]

theorem jet_elliptic_le_of_matrix_le {n : ℕ} {F : Sym n → ℝ} {ell L kappa : ℝ}
    {X H : Sym n} (hell : 0≤ell) (hF : globalElliptic F ell L) (hk : 0≤kappa)
    (hmat : ((H : Mat n)+kappa • (1 : Mat n)-(X : Mat n)).PosSemidef) :
    F X≤F H+kappa*(2*n)*L := by
  let K : Sym n := ⟨kappa • (1 : Mat n),
    IsSelfAdjoint.smul (IsSelfAdjoint.all _) (IsSelfAdjoint.one _)⟩
  have hK : (K : Mat n).PosSemidef := Matrix.PosSemidef.one.smul hk
  have hQ : ((H+K-X : Sym n) : Mat n).PosSemidef := hmat
  have hMono := (hF X (H+K-X) hQ).1
  have hNonneg := mul_nonneg hell hQ.trace_nonneg
  have hEq : X+(H+K-X)=H+K := by abel
  rw [hEq] at hMono
  have hShift := (hF H K hK).2
  have hTrace : Matrix.trace (K : Mat n)=kappa*(2*n) := by
    have hc : (Fintype.card (Yau.RIdx n) : ℝ)=2*n := by simp [Yau.RIdx]; ring
    simp only [K,Matrix.trace_smul,Matrix.trace_one,smul_eq_mul]
    rw [hc]
  rw [hTrace] at hShift
  linarith

end Yau.LeafProofs.L05Aux
