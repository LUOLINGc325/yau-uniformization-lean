import Yau.LeafProofs.L05PerronPolynomials

noncomputable section

open Filter MeasureTheory
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic

def perronDataExtension {n : ℕ} (g : Point n → ℝ) : Point n → ℝ := g ∘ abpRetract

theorem perron_data_extension {n : ℕ} {g : Point n → ℝ} {B : ℝ}
    (hg : ContinuousOn g (unitClosed n)) (hb : ∀ p∈unitClosed n, |g p|≤B) :
    UniformContinuous (perronDataExtension g) ∧
      Set.EqOn (perronDataExtension g) g (unitClosed n) ∧
      ∀ p, |perronDataExtension g p|≤B := by
  have hD : IsCompact (unitClosed n) := (isCompact_closedBall (0 : Space n) 1).prod isCompact_Icc
  refine ⟨?_,?_,?_⟩
  · apply uniformContinuousOn_univ.mp
    exact (hD.uniformContinuousOn_of_continuous hg).comp
      (abpRetract_uniformContinuous n).uniformContinuousOn (fun p _ => abpRetract_mem p)
  · intro p hp
    change g (abpRetract p)=g p
    rw [abpRetract_eq hp]
  · intro p
    exact hb (abpRetract p) (abpRetract_mem p)

theorem perronSeparatedPolynomial_scale {n : ℕ} (c : ℝ) (p : Point n) (v : Space n)
    (a k d A : ℝ) (q : Point n) :
    perronSeparatedPolynomial c p (A • v) (A*a) (A*k) (A*d) q=
      c+A*perronSeparatedPolynomial 0 p v a k d q := by
  rw [perronSeparatedPolynomial_apply,perronSeparatedPolynomial_apply]
  simp only [inner_smul_left,conj_trivial,zero_add]
  ring

theorem perron_barrier_domination {n : ℕ} {D : Set (Point n)} (hD : IsCompact D)
    {G beta : Point n → ℝ} {B eps : ℝ} (hB : 0≤B)
    (hG : ContinuousOn G D) (hb : ∀ q∈D, |G q|≤B)
    {p : Point n} (hp : p∈D) (heps : 0<eps)
    (hbeta : ∀ q∈D, dist q p^2/2≤beta q) :
    ∃ A : ℝ, 0<A ∧ ∀ q∈D,
      G p-eps-A*beta q≤G q ∧ G q≤G p+eps+A*beta q := by
  obtain ⟨rho,hrho,hmod⟩ := Metric.uniformContinuousOn_iff.mp
    (hD.uniformContinuousOn_of_continuous hG) eps heps
  let A := 1+4*B/rho^2
  have hA : 0<A := by dsimp only [A]; positivity
  refine ⟨A,hA,?_⟩
  intro q hq
  have hbetanon : 0≤beta q := (div_nonneg (sq_nonneg _) (by norm_num)).trans (hbeta q hq)
  have hAn : 0≤A*beta q := mul_nonneg hA.le hbetanon
  by_cases hnear : dist q p<rho
  · have hh := hmod q hq p hp hnear
    have hab : |G q-G p|<eps := by simpa only [Real.dist_eq] using hh
    constructor <;> linarith [(abs_lt.mp hab).1,(abs_lt.mp hab).2]
  · have hfar : rho≤dist q p := le_of_not_gt hnear
    have hs : rho^2≤dist q p^2 := pow_le_pow_left₀ hrho.le hfar 2
    have hb2 : rho^2/2≤beta q := (div_le_div_of_nonneg_right hs (by norm_num)).trans (hbeta q hq)
    have hmult := mul_le_mul_of_nonneg_left hb2 hA.le
    have he : A*rho^2=rho^2+4*B := by dsimp only [A]; field_simp
    have hlarge : 2*B≤A*beta q := by nlinarith [sq_nonneg rho]
    have hgp := abs_le.mp (hb p hp)
    have hgq := abs_le.mp (hb q hq)
    constructor <;> linarith

theorem perron_initial_residual {n : ℕ} {ell L : ℝ} {F : Sym n → ℝ}
    (hE : globalElliptic F ell L) (h0 : F 0=0) (p : Point n) (c A : ℝ) (hA : 0≤A)
    (q : Point n) :
    2*A≤timeD Set.univ
        (perronSeparatedPolynomial c p 0 (A*(2+2*(Fintype.card (Yau.RIdx n):ℝ)*L)) A 0) q-
      F (hessian (perronSeparatedPolynomial c p 0 (A*(2+2*(Fintype.card (Yau.RIdx n):ℝ)*L)) A 0) q) ∧
    timeD Set.univ
        (perronSeparatedPolynomial c p 0 ((-A)*(2+2*(Fintype.card (Yau.RIdx n):ℝ)*L)) (-A) 0) q-
      F (hessian (perronSeparatedPolynomial c p 0 ((-A)*(2+2*(Fintype.card (Yau.RIdx n):ℝ)*L)) (-A) 0) q)≤-2*A := by
  have hh := perron_scalar_ellipticity hE h0 (show 0≤2*A by positivity)
  rw [perronSeparatedPolynomial_timeD,perronSeparatedPolynomial_hessian,
    perronSeparatedPolynomial_timeD,perronSeparatedPolynomial_hessian]
  have he : (2*(-A)) • sym (1 : Mat n)= -((2*A) • sym (1 : Mat n)) := by module
  rw [he]
  constructor <;> nlinarith [hh.1.2,hh.2.1]

theorem perron_lateral_residual {n : ℕ} (hn : 0<n) {ell L : ℝ} {F : Sym n → ℝ}
    (hell : 0<ell) (hE : globalElliptic F ell L) (h0 : F 0=0)
    (p : Point n) (hp : p.2∈Set.Ico (-1:ℝ) 1) (c A : ℝ) (hA : 0≤A)
    (q : Point n) (hq : q∈abpClosed n 1 (-1) 1) :
    let K := 3/((Fintype.card (Yau.RIdx n):ℝ)*ell)
    (2*A≤timeD Set.univ
        (perronSeparatedPolynomial c p (A • ((-(1+2*K)) • p.1)) 0 (A*(-K)) A) q-
      F (hessian (perronSeparatedPolynomial c p (A • ((-(1+2*K)) • p.1)) 0 (A*(-K)) A) q)) ∧
    (timeD Set.univ
        (perronSeparatedPolynomial c p ((-A) • ((-(1+2*K)) • p.1)) 0 ((-A)*(-K)) (-A)) q-
      F (hessian (perronSeparatedPolynomial c p ((-A) • ((-(1+2*K)) • p.1)) 0 ((-A)*(-K)) (-A)) q)≤-2*A) := by
  intro K
  have hd : 0<(Fintype.card (Yau.RIdx n):ℝ) := by
    simp only [Yau.RIdx,Fintype.card_prod,Fintype.card_fin,Nat.cast_mul,Nat.cast_ofNat]
    positivity
  have hK : 0<K := by dsimp only [K]; positivity
  have hKeq : K*(Fintype.card (Yau.RIdx n):ℝ)*ell=3 := by
    dsimp only [K]
    field_simp
  have hh := perron_scalar_ellipticity hE h0 (show 0≤2*A*K by positivity)
  have hlow : -2≤q.2-p.2 := by linarith [hq.2.1,hp.2]
  have hhi : q.2-p.2≤2 := by linarith [hq.2.2,hp.1]
  have htl := mul_le_mul_of_nonneg_left hlow (show 0≤2*A by positivity)
  have htu := mul_le_mul_of_nonneg_left hhi (show 0≤2*A by positivity)
  rw [perronSeparatedPolynomial_timeD,perronSeparatedPolynomial_hessian,
    perronSeparatedPolynomial_timeD,perronSeparatedPolynomial_hessian]
  have he : (2*(A*(-K))) • sym (1 : Mat n)= -((2*A*K) • sym (1 : Mat n)) := by module
  have he' : (2*((-A)*(-K))) • sym (1 : Mat n)= (2*A*K) • sym (1 : Mat n) := by module
  rw [he,he']
  have haKeq := congrArg (fun r : ℝ => 2*A*r) hKeq
  constructor <;> nlinarith [hh.1.1,hh.2.2]

end Yau.LeafProofs.L05Aux
