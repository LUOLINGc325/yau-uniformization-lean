import Yau.LeafProofs.L05PerronCalculus

noncomputable section

open Filter MeasureTheory
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic

theorem perron_globalElliptic_mono {n : ℕ} {ell L : ℝ} {F : Sym n → ℝ}
    (hell : 0≤ell) (hE : globalElliptic F ell L) {H K : Sym n}
    (hP : ((K-H : Sym n) : Mat n).PosSemidef) : F H≤F K := by
  have hh := (hE H (K-H) hP).1
  have he : H+(K-H)=K := by abel
  rw [he] at hh
  have hn := mul_nonneg hell hP.trace_nonneg
  linarith

theorem perron_classical_sub {n : ℕ} {ell L : ℝ} {F : Sym n → ℝ}
    (hell : 0<ell) (hE : globalElliptic F ell L)
    {Q : Set (Point n)} {s : Point n → ℝ}
    (hs : ∀ p∈Q, ContDiffAt ℝ 2 s p)
    (hres : ∀ p∈Q, timeD Set.univ s p-F (hessian s p)≤0) :
    viscositySub Q (fun H _ => F H) (fun _ => 0) s := by
  intro p hp phi hphi ht
  obtain ⟨htime,hH⟩ := perron_touch_classical_jets hphi (hs p hp) ht
  have hmono : F (hessian s p)≤F (hessian phi p) :=
    perron_globalElliptic_mono hell.le hE hH
  rw [htime]
  linarith [hres p hp]

theorem perron_classical_super {n : ℕ} {ell L : ℝ} {F : Sym n → ℝ}
    (hell : 0<ell) (hE : globalElliptic F ell L)
    {Q : Set (Point n)} {s : Point n → ℝ}
    (hs : ∀ p∈Q, ContDiffAt ℝ 2 s p)
    (hres : ∀ p∈Q, 0≤timeD Set.univ s p-F (hessian s p)) :
    viscositySuper Q (fun H _ => F H) (fun _ => 0) s := by
  intro p hp phi hphi ht
  obtain ⟨htime,hH⟩ := perron_touch_classical_jets (hs p hp) hphi ⟨ht.1.symm,ht.2⟩
  have hmono : F (hessian phi p)≤F (hessian s p) :=
    perron_globalElliptic_mono hell.le hE hH
  rw [←htime]
  linarith [hres p hp]

theorem perron_timeD_const {n : ℕ} (c : ℝ) (p : Point n) :
    timeD Set.univ (fun _ : Point n => c) p=0 := by simp [timeD]

theorem perron_hessian_const {n : ℕ} (c : ℝ) (p : Point n) :
    hessian (fun _ : Point n => c) p=0 := by
  simp [hessian,spatialDD,spatialD]
  exact (selfAdjointPart ℝ).map_zero

theorem perron_constant_solution {n : ℕ} {ell L : ℝ} {F : Sym n → ℝ}
    (hell : 0<ell) (hE : globalElliptic F ell L) (h0 : F 0=0)
    (Q : Set (Point n)) (c : ℝ) :
    viscositySolution Q (fun H _ => F H) (fun _ => 0) (fun _ => c) := by
  constructor
  · apply perron_classical_sub hell hE (fun p _ => contDiffAt_const)
    intro p hp
    rw [perron_timeD_const,perron_hessian_const,h0]
    norm_num
  · apply perron_classical_super hell hE (fun p _ => contDiffAt_const)
    intro p hp
    rw [perron_timeD_const,perron_hessian_const,h0]
    norm_num

theorem perron_scalar_ellipticity {n : ℕ} {ell L : ℝ} {F : Sym n → ℝ}
    (hE : globalElliptic F ell L) (h0 : F 0=0) {c : ℝ} (hc : 0≤c) :
    (ell*c*(Fintype.card (Yau.RIdx n) : ℝ)≤F (c • sym (1 : Mat n)) ∧
      F (c • sym (1 : Mat n))≤L*c*(Fintype.card (Yau.RIdx n) : ℝ)) ∧
    (-L*c*(Fintype.card (Yau.RIdx n) : ℝ)≤F (-(c • sym (1 : Mat n))) ∧
      F (-(c • sym (1 : Mat n)))≤-ell*c*(Fintype.card (Yau.RIdx n) : ℝ)) := by
  let P : Sym n := c • sym (1 : Mat n)
  have hi : (sym (1 : Mat n) : Mat n)=1 :=
    IsSelfAdjoint.coe_selfAdjointPart_apply ℝ (IsSelfAdjoint.one _)
  have hP : (P : Mat n).PosSemidef := by
    change (c • (sym (1 : Mat n) : Mat n)).PosSemidef
    rw [hi]
    exact Matrix.PosSemidef.one.smul hc
  have htr : Matrix.trace (P : Mat n)=c*(Fintype.card (Yau.RIdx n) : ℝ) := by
    change Matrix.trace (c • (sym (1 : Mat n) : Mat n))=_
    rw [hi,Matrix.trace_smul,smul_eq_mul,Matrix.trace_one]
  have hp := hE 0 P hP
  have hn := hE (-P) P hP
  simp only [zero_add,h0,sub_zero] at hp
  rw [neg_add_cancel,h0,htr] at hn
  rw [htr] at hp
  constructor <;> constructor <;> dsimp only [P] at * <;> linarith [hp.1,hp.2,hn.1,hn.2]

end Yau.LeafProofs.L05Aux
