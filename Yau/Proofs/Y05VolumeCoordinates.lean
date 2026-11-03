import Yau.Proofs.Y05PolynomialEstimates
import Yau.Proofs.Y05Primitive
import Yau.Proofs.Y05InverseBounds
import Yau.Proofs.Y05Growth

noncomputable section

namespace Yau.Proofs.Y05Aux

open Yau Yau.Blueprint.Alignment Yau.Proofs.Y02Aux

variable {n d : ℕ}

/-- The exponential, literal last-coordinate primitive and finite inverse
are all constructed from the coherent scalar tail, with one uniform growth exponent. -/
theorem exists_volume_coordinates
    (hd : 1 ≤ d) (last : Fin n) {ell : ℕ → MvPolynomial (Fin n) ℂ}
    (hzero : ∀ k, (ell k).coeff 0 = 0) {s : ℕ → ℝ}
    (hs : ∀ k, 0 < s k) (hsm : Monotone s)
    (hEllGrowth : HasPolynomialBound s (fun k => polynomialCoeffNorm (ell k))) :
    ∃ (E : ℕ → MvPolynomial (Fin n) ℂ) (A Ainv : ℕ → PolyMap n),
      (∀ k, (E k).totalDegree ≤ d - 1 ∧ (E k).coeff 0 = 1 ∧
        ScalarJetEq (scalarEval (E k)) (fun z => Complex.exp (scalarEval (ell k) z)) (d - 1) ∧
        A k = volumeMap last (E k) ∧ (A k).FixesZero ∧ (Ainv k).FixesZero ∧
        (A k).linearPart = 1 ∧ (A k).degree ≤ d ∧ (Ainv k).degree ≤ d ∧
        PolyMap.JetEq ((A k).comp (Ainv k)) PolyMap.id d ∧
        PolyMap.JetEq ((Ainv k).comp (A k)) PolyMap.id d) ∧
      ∃ C : ℝ, 0 < C ∧ ∀ k, polynomialCoeffNorm (ell k) +
        (A k).coeffNorm + (Ainv k).coeffNorm ≤ (1 + |s k|) ^ C := by
  choose E hEdeg hE0 hEjet hEnorm using (fun k =>
    exists_exponential_polynomial (ell k) (hzero k) (d - 1))
  let A : ℕ → PolyMap n := fun k => volumeMap last (E k)
  let Ainv : ℕ → PolyMap n := fun k => finiteInverseJet (A k) d
  have hAtangent (k : ℕ) : tangentId (A k) :=
    ⟨volumeMap_fixesZero last (E k), volumeMap_linearPart last (E k) (hE0 k)⟩
  have hAdeg (k : ℕ) : (A k).degree ≤ d :=
    (volumeMap_degree last (E k)).trans (by have := hEdeg k; omega)
  have hInv (k : ℕ) := finiteInverseJet_spec (hAtangent k) d
  have hs0 (k : ℕ) : 0 ≤ s k := (hs k).le
  let J := polynomialJetConstant (d - 1)
  let CE := scalarTaylorConstant n (d - 1) * compositionJetConstant (d - 1) *
    exponentialJetConstant (d - 1)
  have hJ : 0 ≤ J := by dsimp [J, polynomialJetConstant]; positivity
  have hCE : 0 ≤ CE := by
    dsimp [CE, scalarTaylorConstant, compositionJetConstant, exponentialJetConstant]
    positivity
  have hL0 (k : ℕ) : 0 ≤ polynomialCoeffNorm (ell k) := polynomialCoeffNorm_nonneg _
  have hJE : HasPolynomialBound s (fun k => J * polynomialCoeffNorm (ell k)) :=
    polynomialBound_mul hs0 (fun _ => hJ) hL0 (polynomialBound_const s J) hEllGrowth
  have hBase : HasPolynomialBound s (fun k => 1 + J * polynomialCoeffNorm (ell k)) :=
    polynomialBound_add hs0 (polynomialBound_const s 1) hJE
  have hPower : HasPolynomialBound s
      (fun k => (1 + J * polynomialCoeffNorm (ell k)) ^ (d - 1)) :=
    polynomialBound_pow hs0 (fun k => by nlinarith [mul_nonneg hJ (hL0 k)]) hBase (d - 1)
  have hEGrowth : HasPolynomialBound s (fun k => polynomialCoeffNorm (E k)) := by
    apply polynomialBound_mono (polynomialBound_mul hs0 (fun _ => hCE)
      (fun k => pow_nonneg (by nlinarith [mul_nonneg hJ (hL0 k)]) _)
      (polynomialBound_const s CE) hPower)
    intro k
    exact hEnorm k
  have hEpos (k : ℕ) : 0 ≤ polynomialCoeffNorm (E k) := polynomialCoeffNorm_nonneg _
  have hAGrowth : HasPolynomialBound s (fun k => (A k).coeffNorm) := by
    apply polynomialBound_mono (polynomialBound_mul hs0 (fun _ => Nat.cast_nonneg n)
      (fun k => by linarith [hEpos k]) (polynomialBound_const s (n : ℝ))
      (polynomialBound_add hs0 (polynomialBound_const s 1) hEGrowth))
    intro k
    exact volumeMap_coeffNorm last (E k)
  have hAPos (k : ℕ) : 0 ≤ (A k).coeffNorm := coeffNorm_nonneg _
  have hInvGrowth : HasPolynomialBound s (fun k => (Ainv k).coeffNorm) := by
    apply polynomialBound_mono (polynomialBound_pow hs0
      (fun k => by linarith [hAPos k, Nat.cast_nonneg (α := ℝ) n])
      (polynomialBound_add hs0 (polynomialBound_const s ((n : ℝ) + 2)) hAGrowth)
      (inverseJetExponent d d))
    intro k
    exact finiteInverseJet_coeffNorm_bound hd (hAdeg k)
  have hTotal := polynomialBound_add hs0
    (polynomialBound_add hs0 hEllGrowth hAGrowth) hInvGrowth
  refine ⟨E, A, Ainv, ?_, polynomialBound_absorb hs hsm hTotal⟩
  intro k
  exact ⟨hEdeg k, hE0 k, hEjet k, rfl, (hAtangent k).1, (hInv k).2.1,
    (hAtangent k).2, hAdeg k, (hInv k).1, (hInv k).2.2.1, (hInv k).2.2.2⟩

end Yau.Proofs.Y05Aux
