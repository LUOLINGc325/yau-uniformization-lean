import Yau.Proofs.Y06CompositionLimits
import Yau.Proofs.Y06SupportAlgebra

/-! The finite coefficient conditions are closed under a common subsequence. -/

noncomputable section

namespace Yau.Proofs.Y06Aux

open Filter MvPolynomial Yau.Proofs.Y02Aux Yau.Blueprint.Alignment
open scoped Topology

variable {n d : ℕ}

theorem coefficientTendsto_unique {p q : ℕ → MvPolynomial (Fin n) ℂ}
    {a b : MvPolynomial (Fin n) ℂ} (hp : CoefficientTendsto p a) (hq : CoefficientTendsto q b)
    (heq : ∀ᶠ H in atTop, p H = q H) : a = b := by
  ext β
  exact tendsto_nhds_unique (hp β) ((hq β).congr' (heq.mono (fun H h => congrArg (fun P => P.coeff β) h.symm)))

theorem coefficientTendsto_degree {P : ℕ → PolyMap n} {Q : PolyMap n}
    (hP : ∀ i, CoefficientTendsto (fun H => P H i) (Q i))
    (hdegree : ∀ᶠ H in atTop, (P H).degree ≤ d) : Q.degree ≤ d := by
  classical
  unfold PolyMap.degree
  apply Finset.sup_le
  intro i hi
  unfold totalDegree
  apply Finset.sup_le
  intro β hβ
  by_contra hn
  have heq : ∀ᶠ H in atTop, (P H i).coeff β = 0 := hdegree.mono
    (fun H h => coeff_zero_of_degree_gt h i β hn)
  have hz : (Q i).coeff β = 0 := tendsto_nhds_unique (hP i β)
    (tendsto_const_nhds.congr' (heq.mono (fun H h => h.symm)))
  exact (mem_support_iff.mp hβ) hz

theorem coefficientTendsto_fixesZero {P : ℕ → PolyMap n} {Q : PolyMap n}
    (hP : ∀ i, CoefficientTendsto (fun H => P H i) (Q i))
    (hzero : ∀ᶠ H in atTop, (P H).FixesZero) : Q.FixesZero := by
  intro i
  exact tendsto_nhds_unique (hP i 0)
    (tendsto_const_nhds.congr' (hzero.mono (fun H h => (h i).symm)))

theorem coefficientTendsto_linearPart {P : ℕ → PolyMap n} {Q : PolyMap n}
    {A : Yau.Blueprint.Herm n}
    (hP : ∀ i, CoefficientTendsto (fun H => P H i) (Q i))
    (hlinear : ∀ᶠ H in atTop, (P H).linearPart = A) : Q.linearPart = A := by
  ext i j
  exact tendsto_nhds_unique (hP i (Finsupp.single j 1))
    (tendsto_const_nhds.congr' (hlinear.mono (fun H h => congrArg (fun M => M i j) h.symm)))

theorem coefficientTendsto_jetEq {P R : ℕ → PolyMap n} {Q S : PolyMap n}
    (hP : ∀ i, CoefficientTendsto (fun H => P H i) (Q i))
    (hR : ∀ i, CoefficientTendsto (fun H => R H i) (S i))
    (hjet : ∀ᶠ H in atTop, PolyMap.JetEq (P H) (R H) d) : PolyMap.JetEq Q S d := by
  intro i β hβ
  exact tendsto_nhds_unique (hP i β)
    ((hR i β).congr' (hjet.mono (fun H h => (h i β hβ).symm)))

theorem coefficientTendsto_allowed {P : ℕ → PolyMap n} {Q : PolyMap n} {w : Fin n → ℝ}
    (hP : ∀ i, CoefficientTendsto (fun H => P H i) (Q i))
    (hallowed : ∀ᶠ H in atTop, Allowed (P H) w) : Allowed Q w := by
  intro i β hβ hn
  by_contra hnot
  have hz : ∀ᶠ H in atTop, (P H i).coeff β = 0 := hallowed.mono (fun H h => by
    by_contra hne
    exact hnot (h i β hβ hne))
  exact hn (tendsto_nhds_unique (hP i β) (tendsto_const_nhds.congr' (hz.mono (fun H h => h.symm))))

theorem coefficientTendsto_onlyForbidden {P : ℕ → PolyMap n} {Q : PolyMap n} {w : Fin n → ℝ}
    (hP : ∀ i, CoefficientTendsto (fun H => P H i) (Q i))
    (hforbidden : ∀ᶠ H in atTop, OnlyForbidden (P H) w) : OnlyForbidden Q w := by
  intro i β hβ hn
  by_contra hnot
  have hz : ∀ᶠ H in atTop, (P H i).coeff β = 0 := hforbidden.mono (fun H h => by
    by_contra hne
    exact hnot (h i β hβ hne))
  exact hn (tendsto_nhds_unique (hP i β) (tendsto_const_nhds.congr' (hz.mono (fun H h => h.symm))))

theorem coefficientTendsto_jacDet {P : ℕ → PolyMap n} {Q : PolyMap n}
    (hP : ∀ i, CoefficientTendsto (fun H => P H i) (Q i)) :
    CoefficientTendsto (fun H => (P H).jacDet) Q.jacDet := by
  classical
  have hdet (R : PolyMap n) : R.jacDet = ∑ σ : Equiv.Perm (Fin n),
      (Equiv.Perm.sign σ : MvPolynomial (Fin n) ℂ) * ∏ i, pderiv i (R (σ i)) :=
    Matrix.det_apply' (jacobianMatrix R)
  simp_rw [hdet]
  apply coefficientTendsto_sum
  intro σ hσ
  apply coefficientTendsto_mul (coefficientTendsto_const _)
  exact coefficientTendsto_prod Finset.univ _ _ (fun i hi => coefficientTendsto_pderiv (hP (σ i)) i)

theorem coefficientTendsto_positiveJacFlat {P : ℕ → PolyMap n} {Q : PolyMap n}
    (hP : ∀ i, CoefficientTendsto (fun H => P H i) (Q i))
    (hflat : ∀ᶠ H in atTop, positiveJacFlat (P H) d) : positiveJacFlat Q d := by
  intro β hβ hβd
  exact tendsto_nhds_unique (coefficientTendsto_jacDet hP β)
    (tendsto_const_nhds.congr' (hflat.mono (fun H h => (h β hβ hβd).symm)))

end Yau.Proofs.Y06Aux
