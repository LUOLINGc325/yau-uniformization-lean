import Yau.LeafProofs.L05PucciHarnackBumpTime

open Filter MeasureTheory Set
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

theorem harnack_bump_minus_lower {n : ℕ} {ell L : ℝ}
    (hell : 0≤ell) (hL : ell≤L) {chi s : ℝ → ℝ} {c : ℝ → Space n}
    (b shift : ℝ) (p : Point n) (hchi : 0≤chi p.2) :
    (chi p.2*Real.exp (-b*(p.2+shift)))*
      (24*ell*max (s p.2-‖p.1-c p.2‖^2) 0*‖p.1-c p.2‖^2-
        6*L*(max (s p.2-‖p.1-c p.2‖^2) 0)^2*(2*n))≤
      harnackPucciMinus ell L (hessian (harnackBump chi s c b shift) p) := by
  let y := p.1-c p.2
  let q := max (s p.2-‖y‖^2) 0
  let k := chi p.2*Real.exp (-b*(p.2+shift))
  have hq : 0≤q := le_max_right _ _
  have hk : 0≤k := mul_nonneg hchi (Real.exp_pos _).le
  let P : Sym n := ⟨(k*(24*q)) • harnackRankOne y,
    IsSelfAdjoint.smul (IsSelfAdjoint.all _) (harnack_rankOne_posSemidef y).isHermitian.isSelfAdjoint⟩
  let N : Sym n := ⟨(k*(6*q^2)) • (1 : Mat n),
    IsSelfAdjoint.smul (IsSelfAdjoint.all _) (IsSelfAdjoint.one _)⟩
  have hP : (P : Mat n).PosSemidef := (harnack_rankOne_posSemidef y).smul (by positivity)
  have hN : (N : Mat n).PosSemidef := Matrix.PosSemidef.one.smul (by positivity)
  have hEq : hessian (harnackBump chi s c b shift) p=P-N := by
    apply Subtype.ext
    rw [harnack_bump_hessian]
    change k • ((24*q) • harnackRankOne y-(6*q^2) • (1 : Mat n))=
      (k*(24*q)) • harnackRankOne y-(k*(6*q^2)) • (1 : Mat n)
    rw [smul_sub,smul_smul,smul_smul]
  have hTraceP : Matrix.trace (P : Mat n)=k*(24*q)*‖y‖^2 := by
    change Matrix.trace ((k*(24*q)) • harnackRankOne y)=_
    rw [Matrix.trace_smul,harnack_rankOne_trace]
    rfl
  have hCard : (Fintype.card (Yau.RIdx n) : ℝ)=2*n := by simp [Yau.RIdx]; ring
  have hTraceN : Matrix.trace (N : Mat n)=k*(6*q^2)*(2*n) := by
    change Matrix.trace ((k*(6*q^2)) • (1 : Mat n))=_
    rw [Matrix.trace_smul,Matrix.trace_one,hCard]
    rfl
  have h := harnack_minus_psd_difference hell hL hP hN
  rw [← hEq,hTraceP,hTraceN] at h
  change k*(24*ell*q*‖y‖^2-6*L*q^2*(2*n))≤_
  convert! h using 1
  ring

def harnackBumpDecay (ell smin A : ℝ) : ℝ := 1+3*A^2/(32*ell*smin)

theorem harnack_bumpDecay_pos {ell smin A : ℝ} (hell : 0<ell) (hsmin : 0<smin) :
    0<harnackBumpDecay ell smin A := by
  unfold harnackBumpDecay
  positivity

theorem harnack_bumpDecay_quadratic {ell smin A : ℝ} (hell : 0<ell) (hsmin : 0<smin) (q : ℝ) :
    A*q-8*ell*smin-(harnackBumpDecay ell smin A/3)*q^2≤0 := by
  let b := harnackBumpDecay ell smin A
  have hb : 0<b := harnack_bumpDecay_pos hell hsmin
  have hRel : (32*ell*smin)*b=32*ell*smin+3*A^2 := by
    dsimp only [b,harnackBumpDecay]
    field_simp [hell.ne',hsmin.ne']
  have hSquare : 0≤(2*b*q-3*A)^2 := sq_nonneg _
  have hNonneg : 0≤ell*smin := mul_nonneg hell.le hsmin.le
  have hProduct : b*(A*q-8*ell*smin-(b/3)*q^2)≤0 := by
    nlinarith only [hRel,hSquare,hNonneg]
  exact nonpos_of_mul_nonpos_right hProduct hb

theorem harnack_bump_residual {n : ℕ} {ell L : ℝ} (hell : 0<ell) (hL : ell≤L)
    {chi s : ℝ → ℝ} {c : ℝ → Space n} (hchi : ContDiff ℝ 2 chi)
    (hs : ContDiff ℝ 2 s) (hc : ContDiff ℝ 2 c)
    {smin kappa R V : ℝ} (hsmin : 0<smin) (shift : ℝ) (p : Point n)
    (hChi : 0≤chi p.2) (hS : smin ≤ s p.2) (hS' : deriv s p.2≤kappa)
    (hY : ‖p.1-c p.2‖≤R) (hC' : ‖deriv c p.2‖≤V) :
    let A := kappa+2*L*(2*n)+2*R*V+8*ell
    let b := harnackBumpDecay ell smin A
    timeD univ (harnackBump chi s c b shift) p-
        harnackPucciMinus ell L (hessian (harnackBump chi s c b shift) p)≤
      deriv chi p.2*Real.exp (-b*(p.2+shift))*harnackPositiveCube (s p.2-‖p.1-c p.2‖^2) := by
  intro A b
  let q := s p.2-‖p.1-c p.2‖^2
  let y := p.1-c p.2
  let k := chi p.2*Real.exp (-b*(p.2+shift))
  by_cases hq : 0<q
  · have hInner : inner ℝ y (deriv c p.2)≤R*V := by
      calc
        _ ≤ ‖y‖*‖deriv c p.2‖ := real_inner_le_norm _ _
        _ ≤ _ := mul_le_mul hY hC' (norm_nonneg _) ((norm_nonneg y).trans hY)
    have hBracket : (deriv s p.2+2*L*(2*n)+2*inner ℝ y (deriv c p.2))*q-
        8*ell*‖y‖^2-(b/3)*q^2≤0 := by
      have hCoef : deriv s p.2+2*L*(2*n)+2*inner ℝ y (deriv c p.2)≤A-8*ell := by
        dsimp only [A]
        linarith
      have hqEq : ‖y‖^2=s p.2-q := by dsimp only [q,y]; ring
      have hBound := mul_le_mul_of_nonneg_right hCoef hq.le
      have hSBound := mul_le_mul_of_nonneg_left hS (by positivity : 0≤8*ell)
      have hQuad := harnack_bumpDecay_quadratic (A := A) hell hsmin q
      change A*q-8*ell*smin-(b/3)*q^2≤0 at hQuad
      rw [hqEq]
      nlinarith only [hBound,hSBound,hQuad]
    have hLower := harnack_bump_minus_lower (s := s) (c := c) hell.le hL b shift p hChi
    have hTime := harnack_bump_timeD hchi hs hc b shift p
    have hLevel : 0<s p.2-‖p.1-c p.2‖^2 := hq
    simp only [harnackPositiveCube,max_eq_left hLevel.le] at hLower hTime ⊢
    change k*(24*ell*q*‖y‖^2-6*L*q^2*(2*n))≤
      harnackPucciMinus ell L (hessian (harnackBump chi s c b shift) p) at hLower
    have hK : 0≤k := mul_nonneg hChi (Real.exp_pos _).le
    calc
      _ ≤ timeD univ (harnackBump chi s c b shift) p-k*(24*ell*q*‖y‖^2-6*L*q^2*(2*n)) :=
        sub_le_sub_left hLower _
      _ = deriv chi p.2*Real.exp (-b*(p.2+shift))*q^3+
          (3*k*q)*((deriv s p.2+2*L*(2*n)+2*inner ℝ y (deriv c p.2))*q-
            8*ell*‖y‖^2-(b/3)*q^2) := by
        rw [hTime]
        dsimp only [q,y,k]
        ring
      _ ≤ deriv chi p.2*Real.exp (-b*(p.2+shift))*q^3 :=
        add_le_of_nonpos_right (mul_nonpos_of_nonneg_of_nonpos (by positivity) hBracket)
  · have hZero := harnack_bump_jets_zero_of_level_nonpos hchi hs hc b shift p (not_lt.mp hq)
    rw [hZero.2.1,hZero.2.2]
    have hP : harnackPositiveCube (s p.2-‖p.1-c p.2‖^2)=0 := by
      have hLevel : s p.2-‖p.1-c p.2‖^2≤0 := not_lt.mp hq
      simp only [harnackPositiveCube,max_eq_right hLevel,zero_pow (by decide : 3≠0)]
    simp only [hP,mul_zero,harnackPucciMinus,neg_zero,pucciPlus_zero hell.le hL,sub_zero,le_refl]

end Yau.LeafProofs.L05Aux
