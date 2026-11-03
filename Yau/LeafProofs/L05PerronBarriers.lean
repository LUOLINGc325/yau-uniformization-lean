import Yau.LeafProofs.L05PerronBarrierBounds

noncomputable section

open Filter MeasureTheory
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic

theorem perron_barriers_of_shape {n : ℕ} {ell L : ℝ} {F : Sym n → ℝ}
    (hell : 0<ell) (hE : globalElliptic F ell L)
    {G : Point n → ℝ} {B eps : ℝ} (hB : 0≤B)
    (hG : ContinuousOn G (abpClosed n 1 (-1) 1))
    (hb : ∀ q∈abpClosed n 1 (-1) 1, |G q|≤B)
    {p : Point n} (hp : p∈abpClosed n 1 (-1) 1) (he : 0<eps)
    (v : Space n) (a k d : ℝ)
    (hshape : ∀ q∈abpClosed n 1 (-1) 1,
      dist q p^2/2≤perronSeparatedPolynomial 0 p v a k d q)
    (hres : ∀ c A : ℝ, 0≤A → ∀ q∈perronOpen n,
      (2*A≤timeD Set.univ (perronSeparatedPolynomial c p (A • v) (A*a) (A*k) (A*d)) q-
        F (hessian (perronSeparatedPolynomial c p (A • v) (A*a) (A*k) (A*d)) q)) ∧
      (timeD Set.univ (perronSeparatedPolynomial c p ((-A) • v) ((-A)*a) ((-A)*k) ((-A)*d)) q-
        F (hessian (perronSeparatedPolynomial c p ((-A) • v) ((-A)*a) ((-A)*k) ((-A)*d)) q)≤-2*A)) :
    ∃ l h : Point n → ℝ,
      ContDiff ℝ ∞ l ∧ ContDiff ℝ ∞ h ∧ l p=G p-eps ∧ h p=G p+eps ∧
      (∀ q∈abpClosed n 1 (-1) 1, l q≤G q ∧ G q≤h q) ∧
      viscositySub (perronOpen n) (fun H _ => F H) (fun _ => 0) l ∧
      viscositySuper (perronOpen n) (fun H _ => F H) (fun _ => 0) h := by
  have hD : IsCompact (abpClosed n 1 (-1) 1) :=
    (isCompact_closedBall (0 : Space n) 1).prod isCompact_Icc
  obtain ⟨A,hA,hdom⟩ := perron_barrier_domination hD hB hG hb hp he hshape
  let l := perronSeparatedPolynomial (G p-eps) p ((-A) • v) ((-A)*a) ((-A)*k) ((-A)*d)
  let h := perronSeparatedPolynomial (G p+eps) p (A • v) (A*a) (A*k) (A*d)
  have hl : ContDiff ℝ ∞ l := perronSeparatedPolynomial_smooth _ _ _ _ _ _
  have hh : ContDiff ℝ ∞ h := perronSeparatedPolynomial_smooth _ _ _ _ _ _
  refine ⟨l,h,hl,hh,perronSeparatedPolynomial_center _ _ _ _ _ _,
    perronSeparatedPolynomial_center _ _ _ _ _ _,?_,?_,?_⟩
  · intro q hq
    dsimp only [l,h]
    rw [perronSeparatedPolynomial_scale,perronSeparatedPolynomial_scale]
    have hd := hdom q hq
    constructor <;> linarith [hd.1,hd.2]
  · apply perron_classical_sub hell hE (fun q _ => hl.contDiffAt.of_le (by simp))
    intro q hq
    have hs := (hres (G p-eps) A hA.le q hq).2
    dsimp only [l]
    linarith
  · apply perron_classical_super hell hE (fun q _ => hh.contDiffAt.of_le (by simp))
    intro q hq
    have hs := (hres (G p+eps) A hA.le q hq).1
    dsimp only [h]
    linarith

theorem perron_boundary_barriers {n : ℕ} (hn : 0<n)
    {ell L : ℝ} (hell : 0<ell) (hL : ell≤L) {F : Sym n → ℝ}
    (hE : globalElliptic F ell L) (h0 : F 0=0)
    {G : Point n → ℝ} {B : ℝ} (hB : 0≤B)
    (hG : ContinuousOn G (abpClosed n 1 (-1) 1))
    (hb : ∀ q∈abpClosed n 1 (-1) 1, |G q|≤B)
    {p : Point n} (hp : p∈perronBoundary n) {eps : ℝ} (he : 0<eps) :
    ∃ l h : Point n → ℝ,
      ContDiff ℝ ∞ l ∧ ContDiff ℝ ∞ h ∧ l p=G p-eps ∧ h p=G p+eps ∧
      (∀ q∈abpClosed n 1 (-1) 1, l q≤G q ∧ G q≤h q) ∧
      viscositySub (perronOpen n) (fun H _ => F H) (fun _ => 0) l ∧
      viscositySuper (perronOpen n) (fun H _ => F H) (fun _ => 0) h := by
  have hpSlab := perronBoundary_subset_slab hp
  have hpD : p∈abpClosed n 1 (-1) 1 := ⟨hpSlab.1,hpSlab.2.1,hpSlab.2.2.le⟩
  rcases hp with hp | hp
  · let kappa := 2+2*(Fintype.card (Yau.RIdx n):ℝ)*L
    have hk : 2≤kappa := by
      have hLp := hell.le.trans hL
      dsimp only [kappa]
      have hh : 0≤2*(Fintype.card (Yau.RIdx n):ℝ)*L := mul_nonneg (by positivity) hLp
      linarith
    apply perron_barriers_of_shape hell hE hB hG hb hpD he 0 kappa 1 0
    · intro q hq
      have hh := perronInitialShape_distance (show p.2=(-1:ℝ) from hp.2) hq hk
      change dist q p^2/2≤perronInitialShape p kappa q
      nlinarith [sq_nonneg (dist q p)]
    · intro c A hA q hq
      simpa only [kappa,smul_zero,mul_one,mul_zero] using perron_initial_residual hE h0 p c A hA q
  · let K := 3/((Fintype.card (Yau.RIdx n):ℝ)*ell)
    have hd : 0<(Fintype.card (Yau.RIdx n):ℝ) := by
      simp only [Yau.RIdx,Fintype.card_prod,Fintype.card_fin,Nat.cast_mul,Nat.cast_ofNat]
      positivity
    have hK : 0<K := by dsimp only [K]; positivity
    have hpn : ‖p.1‖=1 := by simpa only [Metric.mem_sphere,dist_zero_right] using hp.1
    apply perron_barriers_of_shape hell hE hB hG hb hpD he ((-(1+2*K)) • p.1) 0 (-K) 1
    · intro q hq
      exact perronLateralShape_distance hpn hq hK.le
    · intro c A hA q hq
      have hqD : q∈abpClosed n 1 (-1) 1 :=
        ⟨Metric.ball_subset_closedBall hq.1,hq.2.1.le,hq.2.2.le⟩
      simpa only [K,mul_zero,mul_one] using perron_lateral_residual hn hell hE h0 p hp.2 c A hA q hqD

end Yau.LeafProofs.L05Aux
