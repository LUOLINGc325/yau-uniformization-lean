import Yau.Geometry.Polynomial

/-! Coefficient bounds on the actual polynomial maps, including vanishing
of low-degree terms. No polynomial degree or derivative certificate is supplied. -/

open scoped Topology ContDiff

noncomputable section
namespace Yau.NodeProofs.U02Proof

open Yau

theorem vector_norm_le_sum (n : ℕ) (z : ComplexVector n) :
    ‖z‖ ≤ ∑ i, ‖z i‖ := by
  have hz : (∑ i, EuclideanSpace.single i (z i)) = z := by
    ext j
    simp [PiLp.single_apply]
  calc
    ‖z‖ = ‖∑ i, EuclideanSpace.single i (z i)‖ := congrArg norm hz.symm
    _ ≤ ∑ i, ‖EuclideanSpace.single i (z i)‖ := norm_sum_le _ _
    _ = _ := by simp

theorem scalarPolynomial_contDiff {n : ℕ} (P : MvPolynomial (Fin n) ℂ) :
    ContDiff ℂ ⊤ (fun z : ComplexVector n => MvPolynomial.eval (fun i => z i) P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simpa using (contDiff_const : ContDiff ℂ ⊤ (fun _ : ComplexVector n => a))
  | add P Q hP hQ => simpa only [map_add] using hP.add hQ
  | mul_X P i hP =>
    simpa only [map_mul, MvPolynomial.eval_X, EuclideanSpace.coe_proj] using
      hP.mul (EuclideanSpace.proj i).contDiff

theorem polynomial_contDiff {n : ℕ} (P : PolyMap n) : ContDiff ℂ ⊤ P.eval := by
  apply (contDiff_piLp (𝕜 := ℂ) 2).mpr
  intro i
  exact scalarPolynomial_contDiff (P i)

@[simp] theorem polynomial_eval_id {n : ℕ} (z : ComplexVector n) :
    (PolyMap.id : PolyMap n).eval z = z := by
  ext i
  simp [PolyMap.eval, PolyMap.id]

@[simp] theorem polynomial_eval_comp {n : ℕ} (P Q : PolyMap n) (z : ComplexVector n) :
    (P.comp Q).eval z = P.eval (Q.eval z) := by
  ext i
  change MvPolynomial.eval (fun j => z j) (MvPolynomial.bind₁ Q (P i)) =
    MvPolynomial.eval (fun j => MvPolynomial.eval (fun l => z l) (Q j)) (P i)
  exact MvPolynomial.eval₂Hom_bind₁ _ _ _ _

theorem monomial_norm_le {n : ℕ} (m : Fin n →₀ ℕ) (z : ComplexVector n) :
    ‖∏ i ∈ m.support, z i ^ m i‖ ≤ ‖z‖ ^ (m.sum fun _ e => e) := by
  rw [norm_prod]
  calc
    (∏ i ∈ m.support, ‖z i ^ m i‖) ≤ ∏ i ∈ m.support, ‖z‖ ^ m i := by
      apply Finset.prod_le_prod₀
      · intro i hi; positivity
      · intro i hi
        rw [norm_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) (PiLp.norm_apply_le z i) _
    _ = _ := Finset.prod_pow_eq_pow_sum _ _ _

/-- On the unit ball, a scalar polynomial vanishing below degree `q`
has its coefficient norm times the corresponding power bound. -/
theorem scalarPolynomial_norm_le {n q : ℕ} (P : MvPolynomial (Fin n) ℂ)
    (hP : ∀ m : Fin n →₀ ℕ, (m.sum fun _ e => e) < q → P.coeff m = 0)
    {z : ComplexVector n} (hz : ‖z‖ ≤ 1) :
    ‖MvPolynomial.eval (fun i => z i) P‖ ≤
      (∑ m ∈ P.support, ‖P.coeff m‖) * ‖z‖ ^ q := by
  rw [MvPolynomial.eval_eq, Finset.sum_mul]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro m hm
  have hq : q ≤ m.sum (fun _ e => e) := by
    by_contra hn
    exact (MvPolynomial.mem_support_iff.mp hm) (hP m (by omega))
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  exact (monomial_norm_le m z).trans
    (pow_le_pow_of_le_one (norm_nonneg _) hz hq)

/-- The vector estimate uses the literal `PolyMap.coeffNorm` from the models. -/
theorem polynomial_norm_le {n q : ℕ} (P : PolyMap n)
    (hP : ∀ i (m : Fin n →₀ ℕ), (m.sum fun _ e => e) < q → (P i).coeff m = 0)
    {z : ComplexVector n} (hz : ‖z‖ ≤ 1) :
    ‖P.eval z‖ ≤ P.coeffNorm * ‖z‖ ^ q := by
  apply (vector_norm_le_sum n (P.eval z)).trans
  rw [PolyMap.coeffNorm, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  exact scalarPolynomial_norm_le (P i) (hP i) hz

end Yau.NodeProofs.U02Proof
