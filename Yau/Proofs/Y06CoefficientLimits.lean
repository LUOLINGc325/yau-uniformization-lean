import Yau.Proofs.Y06CoefficientCompactness

/-! Coefficientwise limits respect the finite polynomial operations used
in the jet identities and Jacobian determinant. -/

noncomputable section

namespace Yau.Proofs.Y06Aux

open Filter MvPolynomial
open scoped Topology

variable {n : ℕ}

def CoefficientTendsto (p : ℕ → MvPolynomial (Fin n) ℂ) (q : MvPolynomial (Fin n) ℂ) : Prop :=
  ∀ β, Tendsto (fun H => (p H).coeff β) atTop (𝓝 (q.coeff β))

theorem coefficientTendsto_const (p : MvPolynomial (Fin n) ℂ) :
    CoefficientTendsto (fun _ => p) p := fun _ => tendsto_const_nhds

theorem coefficientTendsto_add {p q : ℕ → MvPolynomial (Fin n) ℂ}
    {a b : MvPolynomial (Fin n) ℂ} (hp : CoefficientTendsto p a) (hq : CoefficientTendsto q b) :
    CoefficientTendsto (fun H => p H + q H) (a + b) := by
  intro β
  simpa using (hp β).add (hq β)

theorem coefficientTendsto_sub {p q : ℕ → MvPolynomial (Fin n) ℂ}
    {a b : MvPolynomial (Fin n) ℂ} (hp : CoefficientTendsto p a) (hq : CoefficientTendsto q b) :
    CoefficientTendsto (fun H => p H - q H) (a - b) := by
  intro β
  simpa using (hp β).sub (hq β)

theorem coefficientTendsto_sum {ι : Type*} (S : Finset ι)
    (p : ι → ℕ → MvPolynomial (Fin n) ℂ) (a : ι → MvPolynomial (Fin n) ℂ)
    (hp : ∀ i ∈ S, CoefficientTendsto (p i) (a i)) :
    CoefficientTendsto (fun H => ∑ i ∈ S, p i H) (∑ i ∈ S, a i) := by
  intro β
  simpa only [coeff_sum] using tendsto_finsetSum S (fun i hi => hp i hi β)

theorem coefficientTendsto_mul {p q : ℕ → MvPolynomial (Fin n) ℂ}
    {a b : MvPolynomial (Fin n) ℂ} (hp : CoefficientTendsto p a) (hq : CoefficientTendsto q b) :
    CoefficientTendsto (fun H => p H * q H) (a * b) := by
  classical
  intro β
  simpa only [coeff_mul] using tendsto_finsetSum (Finset.HasAntidiagonal.antidiagonal β)
    (fun t ht => (hp t.1).mul (hq t.2))

theorem coefficientTendsto_pow {p : ℕ → MvPolynomial (Fin n) ℂ}
    {a : MvPolynomial (Fin n) ℂ} (hp : CoefficientTendsto p a) (m : ℕ) :
    CoefficientTendsto (fun H => p H ^ m) (a ^ m) := by
  induction m with
  | zero => simpa only [pow_zero] using coefficientTendsto_const (1 : MvPolynomial (Fin n) ℂ)
  | succ m ih => simpa only [pow_succ] using coefficientTendsto_mul ih hp

theorem coefficientTendsto_prod {ι : Type*} (S : Finset ι)
    (p : ι → ℕ → MvPolynomial (Fin n) ℂ) (a : ι → MvPolynomial (Fin n) ℂ)
    (hp : ∀ i ∈ S, CoefficientTendsto (p i) (a i)) :
    CoefficientTendsto (fun H => ∏ i ∈ S, p i H) (∏ i ∈ S, a i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty] using coefficientTendsto_const (1 : MvPolynomial (Fin n) ℂ)
  | @insert i S hi ih =>
    simpa only [Finset.prod_insert hi] using coefficientTendsto_mul
      (hp i (Finset.mem_insert_self _ _)) (ih (fun j hj => hp j (Finset.mem_insert_of_mem hj)))

theorem coefficientTendsto_pderiv {p : ℕ → MvPolynomial (Fin n) ℂ}
    {a : MvPolynomial (Fin n) ℂ} (hp : CoefficientTendsto p a) (i : Fin n) :
    CoefficientTendsto (fun H => pderiv i (p H)) (pderiv i a) := by
  intro β
  simpa only [coeff_pderiv] using (hp (β + Finsupp.single i 1)).mul tendsto_const_nhds

end Yau.Proofs.Y06Aux
