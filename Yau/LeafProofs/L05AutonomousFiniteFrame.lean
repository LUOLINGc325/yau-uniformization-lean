import Yau.LeafProofs.L05AutonomousLocalFrame

noncomputable section
open scoped Topology Matrix Matrix.Norms.Frobenius
open Finset Matrix Set
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic Yau.LeafProofs.L05Aux

/-- Compactness only chooses finitely many actual local spectral frames. -/
theorem auto_finite_nonnegative_directions
    (n : ℕ) (hn : 0<n) (ell L : ℝ) (hell : 0<ell) (hL : ell≤L) :
    ∃ N : ℕ, 0<N ∧ ∃ e : Fin N → Space n,
      (∀ j, ‖e j‖=1) ∧
      (∀ A ∈ slopeSet n (ell/2) L, ∃ beta : Fin N → ℝ,
        (∀ j, beta j∈Icc 0 (2*L)) ∧ A=∑ j, beta j • autoRankOne (e j)) ∧
      (∀ i : Yau.RIdx n, ∃ k, e k=Yau.realVec i) ∧
      (∀ i j : Yau.RIdx n, i≠j → ∃ k, e k=autoPairDirection i j) := by
  classical
  let K := slopeSet n (ell/2) L
  have hlocal (B : K) : ∃ U : Set (Sym n), IsOpen U ∧ (B : Sym n)∈U ∧
      ∀ H∈U, ∀ q, autoLocalCoefficient (ell/(8*(2*n)))
        (autoBasisMatrix (autoEigenBasis (B : Sym n)) H) q∈Ioo 0 (2*L) := by
    exact autoLocal_positive_neighborhood hn hell hL _ _
      (autoEigenBasis_slope_diagonal_bounds (B : Sym n) B.property)
      (fun i j hij => by simp only [autoEigenBasis_diagonal,ite_eq_right hij])
  choose U hU hBU hcoef using hlocal
  have hcover : K⊆⋃ B : K, U B := by
    intro B hB
    exact mem_iUnion.mpr ⟨⟨B,hB⟩,hBU ⟨B,hB⟩⟩
  obtain ⟨s,hs⟩ := (slopeSet_isCompact n (by linarith only [hell] : 0≤ell/2)).elim_finite_subcover U hU hcover
  let I := {B : K // B∈s}
  let J := (I × AutoLocalIndex n) ⊕ (Yau.RIdx n × Yau.RIdx n)
  let d : J → Space n := fun q => match q with
    | .inl (B,j) => autoLocalDirection (autoEigenBasis (B.val.val : Sym n)) j
    | .inr (i,j) => if i=j then Yau.realVec i else autoPairDirection i j
  let eqv := Fintype.equivFin J
  let N := Fintype.card J
  let e : Fin N → Space n := fun k => d (eqv.symm k)
  have hN : 0<N := by
    let i : Yau.RIdx n := (⟨0,hn⟩,0)
    exact Fintype.card_pos_iff.mpr ⟨Sum.inr (i,i)⟩
  have hd (q : J) : ‖d q‖=1 := by
    rcases q with ⟨B,j⟩ | ⟨i,j⟩
    · exact autoLocalDirection_norm _ _
    by_cases hij : i=j
    · simpa only [d,ite_eq_left hij] using auto_realVec_norm i
    simpa only [d,ite_eq_right hij] using autoPairDirection_norm hij
  refine ⟨N,hN,e,fun j => hd (eqv.symm j),?_,?_,?_⟩
  · intro A hA
    obtain ⟨B,hBs,hAU⟩ := mem_iUnion₂.mp (hs hA)
    let B0 : I := ⟨B,hBs⟩
    let beta0 : AutoLocalIndex n → ℝ := fun q =>
      autoLocalCoefficient (ell/(8*(2*n))) (autoBasisMatrix (autoEigenBasis (B : Sym n)) A) q
    let betaJ : J → ℝ := fun q => match q with
      | .inl (B',j) => if B'=B0 then beta0 j else 0
      | .inr _ => 0
    have hbetaJ (q : J) : betaJ q∈Icc 0 (2*L) := by
      rcases q with ⟨B',j⟩ | ⟨i,j⟩
      · by_cases hBB : B'=B0
        · simpa only [betaJ,ite_eq_left hBB] using
            ⟨(hcoef B A hAU j).1.le,(hcoef B A hAU j).2.le⟩
        simp only [betaJ,ite_eq_right hBB,Set.mem_Icc,le_refl,true_and]
        linarith only [hell,hL]
      simp only [betaJ,Set.mem_Icc,le_refl,true_and]
      linarith only [hell,hL]
    refine ⟨fun k => betaJ (eqv.symm k),fun k => hbetaJ (eqv.symm k),?_⟩
    have hreindex : (∑ k : Fin N, betaJ (eqv.symm k) • autoRankOne (e k))=
        ∑ q : J, betaJ q • autoRankOne (d q) := by
      exact eqv.symm.sum_comp (fun q : J => betaJ q • autoRankOne (d q))
    rw [hreindex]
    have hsum : (∑ q : J, betaJ q • autoRankOne (d q))=
        ∑ j, beta0 j • autoRankOne (autoLocalDirection (autoEigenBasis (B : Sym n)) j) := by
      rw [Fintype.sum_sum_type]
      have hzero : (∑ q : Yau.RIdx n × Yau.RIdx n,
          betaJ (.inr q) • autoRankOne (d (.inr q)))=0 := by
        simp only [betaJ,zero_smul,Finset.sum_const_zero]
      rw [hzero,add_zero]
      calc
        _ = ∑ j : AutoLocalIndex n, ∑ B' : I,
            betaJ (.inl (B',j)) • autoRankOne (d (.inl (B',j))) := by
          rw [Fintype.sum_prod_type,Finset.sum_comm]
        _ = _ := by
          apply Finset.sum_congr rfl
          intro j _
          simp only [betaJ,d,ite_smul,zero_smul]
          rw [Finset.sum_ite_eq',if_pos (Finset.mem_univ B0)]
    rw [hsum]
    exact autoLocal_actual_representation _ _ A
  · intro i
    refine ⟨eqv (.inr (i,i)),?_⟩
    simp only [e,Equiv.symm_apply_apply,d,ite_true]
  · intro i j hij
    refine ⟨eqv (.inr (i,j)),?_⟩
    simp only [e,Equiv.symm_apply_apply,d,ite_eq_right hij]

/-- A single fixed finite positive frame works for every elliptic matrix, and also
reconstructs the norm of every symmetric matrix. All choices precede the matrix. -/
theorem auto_finite_positive_directions
    (n : ℕ) (hn : 0<n) (ell L : ℝ) (hell : 0<ell) (hL : ell≤L) :
    ∃ N : ℕ, 0<N ∧ ∃ e : Fin N → Space n, ∃ a b : ℝ,
      0<a ∧ a≤b ∧ (∀ j, ‖e j‖=1) ∧
      (∀ A ∈ slopeSet n ell L, ∃ beta : Fin N → ℝ,
        (∀ j, beta j∈Icc a b) ∧ A=∑ j, beta j • autoRankOne (e j)) ∧
      (∀ H : Sym n, ‖H‖≤(2*n:ℝ)*2*∑ j, |tracePair (autoRankOne (e j)) H|) := by
  obtain ⟨N,hN,e,he,hrep,hdiag,hpair⟩ := auto_finite_nonnegative_directions n hn ell L hell hL
  obtain ⟨ha,hab,hpos⟩ := auto_positive_frame_absorption hN hell hL e he hrep
  exact ⟨N,hN,e,ell/(4*N),3*L,ha,hab,he,hpos,
    auto_direction_reconstruction e hdiag hpair⟩

end Yau.LeafProofs.L05AutonomousAux
