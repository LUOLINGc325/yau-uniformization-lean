import Yau.Proofs.Y01DirectionalCoefficients

/-! A fixed finite coefficient norm is bounded by the actual Fréchet jet norm. -/

noncomputable section

namespace Yau.Proofs.Y01Aux

open MvPolynomial Yau.Proofs.Y02Aux
open scoped ContDiff

variable {n : ℕ}

def boundedMonomials (n d : ℕ) : Finset (Fin n →₀ ℕ) := by
  classical
  exact Finset.univ.image (fun a : Fin n → Fin (d + 1) =>
    Finsupp.equivFunOnFinite.symm (fun i => (a i : ℕ)))

theorem monomial_mem_bounded {a : Fin n →₀ ℕ} {d : ℕ} (ha : a.degree ≤ d) :
    a ∈ boundedMonomials n d := by
  classical
  have hbound (i : Fin n) : a i ≤ d := by
    have hi : a i ≤ a.degree := by
      by_cases hz : a i = 0
      · rw [hz]
        exact Nat.zero_le _
      · change a i ≤ ∑ j ∈ a.support, a j
        exact Finset.single_le_sum (fun j hj => Nat.zero_le _) (Finsupp.mem_support_iff.2 hz)
    exact hi.trans ha
  apply Finset.mem_image.2
  refine ⟨fun i => ⟨a i, by have := hbound i; omega⟩, Finset.mem_univ _, ?_⟩
  ext i
  rfl

theorem scalar_projection_jet_norm (P : PolyMap n) (i : Fin n) (m : ℕ) :
    ‖iteratedFDeriv ℂ m (polyEval (P i)) 0‖ ≤ ‖iteratedFDeriv ℂ m P.eval 0‖ := by
  let L : ComplexVector n →L[ℂ] ℂ := EuclideanSpace.proj i
  have hL : ‖L‖ ≤ 1 := L.opNorm_le_bound (by norm_num) (fun z => by
    simpa only [L, coordinate_proj_apply, one_mul] using (PiLp.norm_apply_le z i))
  have hderiv := L.iteratedFDeriv_comp_left (x := 0)
    ((polyMap_eval_contDiff P).of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt
    (le_refl (m : WithTop ℕ∞))
  change iteratedFDeriv ℂ m (polyEval (P i)) 0 =
    L.compContinuousMultilinearMap (iteratedFDeriv ℂ m P.eval 0) at hderiv
  rw [hderiv]
  exact (L.norm_compContinuousMultilinearMap_le _).trans
    ((mul_le_mul_of_nonneg_right hL (norm_nonneg _)).trans_eq (one_mul _))

theorem coefficient_norm_le_jetNorm (P : PolyMap n) {d : ℕ} (hdeg : P.degree ≤ d)
    (i : Fin n) (a : Fin n →₀ ℕ) : ‖(P i).coeff a‖ ≤ jetNorm P.eval d := by
  by_cases hz : (P i).coeff a = 0
  · rw [hz, norm_zero]
    unfold jetNorm
    positivity
  · have ha : a.degree ≤ d := (le_totalDegree (mem_support_iff.2 hz)).trans
      ((component_degree_le P i).trans hdeg)
    apply (scalar_coeff_norm_le_jet (P i) a).trans
    apply (scalar_projection_jet_norm P i a.degree).trans
    unfold jetNorm
    exact Finset.single_le_sum (fun k hk => norm_nonneg (iteratedFDeriv ℂ k P.eval 0))
      (Finset.mem_range.2 (by omega : a.degree < d + 1))

theorem coeffNorm_le_jetNorm (P : PolyMap n) {d : ℕ} (hdeg : P.degree ≤ d) :
    P.coeffNorm ≤ ((n : ℝ) * ((boundedMonomials n d).card : ℝ)) * jetNorm P.eval d := by
  classical
  have hcomponent (i : Fin n) : polynomialCoeffNorm (P i) ≤
      ((boundedMonomials n d).card : ℝ) * jetNorm P.eval d := by
    have hs : (P i).support ⊆ boundedMonomials n d := by
      intro a ha
      exact monomial_mem_bounded ((le_totalDegree ha).trans ((component_degree_le P i).trans hdeg))
    rw [← sum_norm_coeff_eq (P i) (boundedMonomials n d) hs]
    calc
      _ ≤ ∑ a ∈ boundedMonomials n d, jetNorm P.eval d :=
        Finset.sum_le_sum (fun a ha => coefficient_norm_le_jetNorm P hdeg i a)
      _ = _ := by simp
  change (∑ i, polynomialCoeffNorm (P i)) ≤ _
  calc
    _ ≤ ∑ _i : Fin n, ((boundedMonomials n d).card : ℝ) * jetNorm P.eval d :=
      Finset.sum_le_sum (fun i hi => hcomponent i)
    _ = _ := by simp [mul_assoc]

theorem jetNorm_eq_of_germJetEq {f g : ComplexVector n → ComplexVector n} {d : ℕ}
    (h : GermJetEq f g d) : jetNorm f d = jetNorm g d := by
  unfold jetNorm
  apply Finset.sum_congr rfl
  intro m hm
  exact congrArg norm (h m (by have := Finset.mem_range.1 hm; omega))

end Yau.Proofs.Y01Aux
