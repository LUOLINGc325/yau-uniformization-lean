import Yau.LeafProofs.L05SlopeCompact

noncomputable section
open scoped Topology Matrix Matrix.Norms.Frobenius
open Finset Matrix

namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic Yau.LeafProofs.L05Aux

/-- The actual rank-one symmetric matrix in the fixed real orthonormal coordinates. -/
def autoRankOne {n : ℕ} (e : Space n) : Sym n :=
  sym (fun i j => inner ℝ (Yau.realVec i) e * inner ℝ (Yau.realVec j) e)

theorem autoRankOne_coe {n : ℕ} (e : Space n) :
    (autoRankOne e : Mat n) =
      fun i j => inner ℝ (Yau.realVec i) e * inner ℝ (Yau.realVec j) e := by
  apply IsSelfAdjoint.coe_selfAdjointPart_apply
  apply Matrix.isHermitian_iff_isSelfAdjoint.mp
  apply Matrix.IsHermitian.ext
  intro i j
  simp only [star_trivial]
  ring

theorem autoRankOne_posSemidef {n : ℕ} (e : Space n) :
    (autoRankOne e : Mat n).PosSemidef := by
  rw [autoRankOne_coe]
  have heq : (fun i j => inner ℝ (Yau.realVec i) e * inner ℝ (Yau.realVec j) e) =
      Matrix.vecMulVec (fun i => inner ℝ (Yau.realVec i) e)
        (star (fun i => inner ℝ (Yau.realVec i) e)) := by
    ext i j
    simp [Matrix.vecMulVec_apply]
  rw [heq]
  exact Matrix.posSemidef_vecMulVec_self_star _

theorem auto_realVec_inner {n : ℕ} (i j : Yau.RIdx n) :
    inner ℝ (Yau.realVec i) (Yau.realVec j) = if i=j then 1 else 0 := by
  simpa only [complexVector_realOrthonormalBasis_apply] using
    (complexVector_realOrthonormalBasis n).inner_eq_ite i j

theorem auto_realVec_norm {n : ℕ} (i : Yau.RIdx n) : ‖Yau.realVec i‖ = 1 := by
  simpa only [complexVector_realOrthonormalBasis_apply] using
    (complexVector_realOrthonormalBasis n).orthonormal.norm_eq_one i

theorem autoRankOne_trace {n : ℕ} (e : Space n) :
    Matrix.trace (autoRankOne e : Mat n) = ‖e‖^2 := by
  rw [autoRankOne_coe]
  change (∑ i, inner ℝ (Yau.realVec i) e * inner ℝ (Yau.realVec i) e) = ‖e‖^2
  simpa only [← pow_two,
    complexVector_realOrthonormalBasis_apply, real_inner_comm, real_inner_self_eq_norm_sq] using
    (complexVector_realOrthonormalBasis n).sum_inner_mul_inner e e

theorem auto_tracePair_rankOne {n : ℕ} (e : Space n) (H : Sym n) :
    tracePair (autoRankOne e) H =
      ∑ i, ∑ j, (H : Mat n) i j * inner ℝ (Yau.realVec i) e *
        inner ℝ (Yau.realVec j) e := by
  have hs (i j) : (H : Mat n) j i = (H : Mat n) i j := by
    simpa only [star_trivial] using
      (Matrix.isHermitian_iff_isSelfAdjoint.mpr H.property).apply i j
  simp only [tracePair, autoRankOne_coe, Matrix.trace, Matrix.diag_apply,
    Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hs]
  ring

theorem auto_tracePair_realVec {n : ℕ} (i : Yau.RIdx n) (H : Sym n) :
    tracePair (autoRankOne (Yau.realVec i)) H = (H : Mat n) i i := by
  rw [auto_tracePair_rankOne]
  simp [auto_realVec_inner]

/-- A normalized sum of two distinct orthogonal coordinate directions. -/
def autoPairDirection {n : ℕ} (i j : Yau.RIdx n) : Space n :=
  (Real.sqrt 2)⁻¹ • (Yau.realVec i + Yau.realVec j)

theorem autoPairDirection_norm {n : ℕ} {i j : Yau.RIdx n} (hij : i≠j) :
    ‖autoPairDirection i j‖ = 1 := by
  have hsq : ‖Yau.realVec i + Yau.realVec j‖^2 = 2 := by
    rw [norm_add_sq_real, auto_realVec_norm, auto_realVec_norm, auto_realVec_inner,
      ite_eq_right hij]
    norm_num
  have hnorm : ‖Yau.realVec i + Yau.realVec j‖ = Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤2),
      Real.sqrt_nonneg (2:ℝ), norm_nonneg (Yau.realVec i+Yau.realVec j)]
  rw [autoPairDirection, norm_smul, Real.norm_eq_abs, abs_inv,
    abs_of_nonneg (Real.sqrt_nonneg 2), hnorm, inv_mul_cancel₀ (by positivity)]

theorem auto_tracePair_pair {n : ℕ} {i j : Yau.RIdx n} (hij : i≠j) (H : Sym n) :
    tracePair (autoRankOne (autoPairDirection i j)) H =
      ((H : Mat n) i i + (H : Mat n) j j)/2 + (H : Mat n) i j := by
  have hs : (H : Mat n) j i = (H : Mat n) i j := by
    simpa only [star_trivial] using
      (Matrix.isHermitian_iff_isSelfAdjoint.mpr H.property).apply i j
  rw [auto_tracePair_rankOne]
  simp only [autoPairDirection, inner_smul_right, inner_add_right,
    auto_realVec_inner]
  simp only [mul_add, add_mul, Finset.sum_add_distrib, mul_ite, ite_mul,
    mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp only [zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [hs]
  have hsqrt : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  have hne : Real.sqrt 2≠0 := by positivity
  field_simp
  rw [hsqrt]
  ring

theorem auto_matrix_norm_le_entry_bound {n : ℕ} (H : Sym n) {B : ℝ} (hB : 0≤B)
    (hentry : ∀ i j, |(H : Mat n) i j|≤B) : ‖H‖≤(2*n : ℝ)*B := by
  have hs : ‖H‖^2 ≤ ((2*n : ℝ)*B)^2 := by
    change ‖(H : Mat n)‖^2≤_
    rw [frobenius_norm_sq]
    calc
      _ ≤ ∑ _i : Yau.RIdx n, ∑ _j : Yau.RIdx n, B^2 := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        nlinarith only [hentry i j, neg_le_abs ((H : Mat n) i j),
          le_abs_self ((H : Mat n) i j), sq_nonneg (B-|(H : Mat n) i j|),
          sq_abs ((H : Mat n) i j)]
      _ = _ := by simp [Yau.RIdx]; ring
  nlinarith only [hs, norm_nonneg H, mul_nonneg (by positivity : (0:ℝ)≤2*n) hB]

/-- Literal finite coordinate directions suffice to reconstruct the actual Frobenius norm. -/
theorem auto_direction_reconstruction {n N : ℕ} (e : Fin N → Space n)
    (hdiag : ∀ i : Yau.RIdx n, ∃ k, e k=Yau.realVec i)
    (hpair : ∀ i j : Yau.RIdx n, i≠j → ∃ k, e k=autoPairDirection i j)
    (H : Sym n) :
    ‖H‖≤(2*n : ℝ)*2*(∑ k, |tracePair (autoRankOne (e k)) H|) := by
  let S := ∑ k, |tracePair (autoRankOne (e k)) H|
  have hS : 0≤S := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hd (i : Yau.RIdx n) : |(H : Mat n) i i|≤S := by
    obtain ⟨k,hk⟩ := hdiag i
    have hh := Finset.single_le_sum (f := fun k => |tracePair (autoRankOne (e k)) H|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ k)
    simpa only [hk, auto_tracePair_realVec] using hh
  have he (i j : Yau.RIdx n) : |(H : Mat n) i j|≤2*S := by
    by_cases hij : i=j
    · subst j
      linarith only [hd i, hS]
    obtain ⟨k,hk⟩ := hpair i j hij
    have hp : |((H : Mat n) i i+(H : Mat n) j j)/2+(H : Mat n) i j|≤S := by
      have hh := Finset.single_le_sum (f := fun k => |tracePair (autoRankOne (e k)) H|)
        (fun _ _ => abs_nonneg _) (Finset.mem_univ k)
      simpa only [hk, auto_tracePair_pair hij] using hh
    have hi := abs_le.mp (hd i)
    have hj := abs_le.mp (hd j)
    exact abs_le.mpr ⟨by linarith only [(abs_le.mp hp).1, hi.2, hj.2],
      by linarith only [(abs_le.mp hp).2, hi.1, hj.1]⟩
  calc
    ‖H‖ ≤ (2*n : ℝ)*(2*S) := auto_matrix_norm_le_entry_bound H (by positivity) he
    _ = _ := by dsimp only [S]; ring

/-- A unit rank-one projector is bounded above by the identity, in the actual PSD order. -/
theorem autoRankOne_le_one {n : ℕ} (e : Space n) (he : ‖e‖=1) :
    ((1 : Mat n)-(autoRankOne e : Mat n)).PosSemidef := by
  classical
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · exact Matrix.isHermitian_one.sub (autoRankOne_posSemidef e).isHermitian
  intro v
  let c : Yau.RIdx n → ℝ := fun i => inner ℝ (Yau.realVec i) e
  have hc : (∑ i, (c i)^2)=1 := by
    have hh := autoRankOne_trace e
    rw [he] at hh
    rw [autoRankOne_coe] at hh
    change (∑ i, c i*c i)=1^2 at hh
    simpa only [pow_two,one_mul] using hh
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ c v
  rw [hc,one_mul] at hcs
  rw [autoRankOne_coe]
  change 0≤v ⬝ᵥ (((1 : Mat n)-Matrix.vecMulVec c c) *ᵥ v)
  rw [Matrix.sub_mulVec,Matrix.one_mulVec,Matrix.vecMulVec_mulVec]
  simp only [dotProduct, Pi.sub_apply, Pi.smul_apply, MulOpposite.smul_eq_mul_unop,
    MulOpposite.unop_op, mul_sub, Finset.sum_sub_distrib, ← pow_two,
    ← Finset.sum_mul]
  have hcomm : (∑ i, v i*c i)=(∑ i, c i*v i) := by
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  simp only [← mul_assoc, ← Finset.sum_mul]
  rw [hcomm]
  nlinarith only [hcs]

/-- A finite sum of unit rank-one matrices has the explicit upper budget N I. -/
theorem autoRankOne_sum_budget {n N : ℕ} (e : Fin N → Space n)
    (he : ∀ j, ‖e j‖=1) :
    ((N : ℝ) • (1 : Mat n) - ∑ j, (autoRankOne (e j) : Mat n)).PosSemidef := by
  have hh : (∑ j : Fin N, ((1 : Mat n)-(autoRankOne (e j) : Mat n))).PosSemidef := by
    exact Matrix.posSemidef_sum _ fun j _ => autoRankOne_le_one (e j) (he j)
  simpa only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_smul_eq_nsmul] using hh

/-- Absorb a uniform positive coefficient into every direction. The input representation
is on the enlarged ellipticity compact set and allows zero coefficients; the output on
the original compact set has the explicit strictly positive budget ell/(4N). -/
theorem auto_positive_frame_absorption {n N : ℕ} (hN : 0<N)
    {ell L : ℝ} (hell : 0<ell) (hL : ell≤L) (e : Fin N → Space n)
    (he : ∀ j, ‖e j‖=1)
    (hrep : ∀ A ∈ slopeSet n (ell/2) L, ∃ beta : Fin N → ℝ,
      (∀ j, beta j ∈ Set.Icc 0 (2*L)) ∧ A=∑ j, beta j • autoRankOne (e j)) :
    let a := ell/(4*N)
    0<a ∧ a≤3*L ∧ ∀ A ∈ slopeSet n ell L, ∃ beta : Fin N → ℝ,
      (∀ j, beta j ∈ Set.Icc a (3*L)) ∧ A=∑ j, beta j • autoRankOne (e j) := by
  classical
  dsimp only
  let a : ℝ := ell/(4*N)
  have hNr : (0:ℝ)<N := by exact_mod_cast hN
  have ha : 0<a := by dsimp only [a]; positivity
  have haN : a*N=ell/4 := by dsimp only [a]; field_simp
  have haL : a≤L := by
    have hN1 : (1:ℝ)≤N := by exact_mod_cast hN
    have haell : a≤ell := by nlinarith only [haN, hN1, ha.le, hell.le]
    exact haell.trans hL
  refine ⟨ha,by linarith only [haL,hell,hL],?_⟩
  intro A hA
  let S : Sym n := ∑ j, autoRankOne (e j)
  let D : Sym n := A-a • S
  have hS : (S : Mat n).PosSemidef := by
    simpa only [S, AddSubmonoidClass.coe_finsetSum] using
      (Matrix.posSemidef_sum Finset.univ fun j _ => autoRankOne_posSemidef (e j))
  have hbudget : ((N:ℝ) • (1 : Mat n)-(S : Mat n)).PosSemidef := by
    simpa only [S, AddSubmonoidClass.coe_finsetSum] using autoRankOne_sum_budget e he
  have hD : D ∈ slopeSet n (ell/2) L := by
    constructor
    · have hrem : 0≤ell/2-a*N := by rw [haN]; linarith only [hell]
      have hh := (hA.1.add (hbudget.smul ha.le)).add (Matrix.PosSemidef.one.smul hrem)
      convert hh using 1
      change (A : Mat n)-a • (S : Mat n)-(ell/2) • (1 : Mat n)=_
      rw [smul_sub,smul_smul]
      module
    · have hh := hA.2.add (hS.smul ha.le)
      convert hh using 1
      change L • (1 : Mat n)-((A : Mat n)-a • (S : Mat n))=_
      abel
  obtain ⟨beta,hbeta,hDbeta⟩ := hrep D hD
  refine ⟨fun j => beta j+a,fun j => ⟨by linarith only [(hbeta j).1],
    by linarith only [(hbeta j).2,haL]⟩,?_⟩
  calc
    A = D+a • S := by dsimp only [D]; abel
    _ = (∑ j, beta j • autoRankOne (e j))+∑ j, a • autoRankOne (e j) := by
      rw [hDbeta]
      dsimp only [S]
      rw [Finset.smul_sum]
    _ = ∑ j, (beta j+a) • autoRankOne (e j) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun _ _ => (add_smul _ _ _).symm

end Yau.LeafProofs.L05AutonomousAux
