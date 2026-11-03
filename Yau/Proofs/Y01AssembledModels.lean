import Yau.Proofs.Y01RegularTransition

/-! The actual model sequence uses the original Y06 model on active
regular steps and the original Y02 realization on all remaining steps. -/

noncomputable section

attribute [local instance] Classical.propDecidable

namespace Yau.Proofs.Y01Aux

open Yau.Blueprint Yau.Blueprint.Alignment Yau.Proofs.Y02Aux

variable {n d : ℕ}

def assembledModel (active : ℕ → Prop) (J : ℕ → Herm n) (qsol : JetData n)
    (R : ℕ → PolyMap n) (k : ℕ) : PolyMap n :=
  if active k then (linearPoly (J k)).comp (qsol.model k) else R k

def assembledInverseModel (active : ℕ → Prop) (J : ℕ → Herm n) (qsol : JetData n)
    (Rinv : ℕ → PolyMap n) (k : ℕ) : PolyMap n :=
  if active k then (qsol.inverseModel k).comp (linearPoly (J k)⁻¹) else Rinv k

theorem original_realizations_on_all_steps
    {Dd : ℕ} {Craw : ℝ} {Jet : ℕ → PolyMap n}
    (hrealize : ∀ P : PolyMap n, IsConstantVolumeJet P d →
      ∃ G Ginv : PolyMap n, IsPolyAutomorphism G Ginv ∧ PolyMap.JetEq G P d ∧
        G.degree ≤ Dd ∧ Ginv.degree ≤ Dd ∧
        G.coeffNorm + Ginv.coeffNorm ≤ Craw * (1 + P.coeffNorm + matOpNorm P.linearPart⁻¹) ^ Craw)
    (hJet : ∀ k, IsConstantVolumeJet (Jet k) d) :
    ∃ R Rinv : ℕ → PolyMap n, ∀ k,
      IsPolyAutomorphism (R k) (Rinv k) ∧ PolyMap.JetEq (R k) (Jet k) d ∧
        (R k).degree ≤ Dd ∧ (Rinv k).degree ≤ Dd ∧
        (R k).coeffNorm + (Rinv k).coeffNorm ≤
          Craw * (1 + (Jet k).coeffNorm + matOpNorm (Jet k).linearPart⁻¹) ^ Craw := by
  choose R Rinv hR using (fun k => hrealize (Jet k) (hJet k))
  exact ⟨R, Rinv, hR⟩

theorem assembled_models_automorphisms
    {Fhat : ℕ → ComplexVector n → ComplexVector n} {Djet Jjet J : ℕ → Herm n}
    {w : ℕ → Fin n → ℝ} {active : ℕ → Prop} {Dstar : ℕ} {s : ℕ → ℝ}
    {C : ℝ} {qsol : JetData n} {R Rinv : ℕ → PolyMap n}
    (hQ : RegularJetSolution Fhat Djet Jjet w active d Dstar s C qsol)
    (hJ : ∀ k, active k → IsUnit (J k)) (hR : ∀ k, IsPolyAutomorphism (R k) (Rinv k)) :
    ∀ k, IsPolyAutomorphism (assembledModel active J qsol R k)
      (assembledInverseModel active J qsol Rinv k) := by
  intro k
  by_cases hk : active k
  · obtain ⟨hqlin, hqdegree, hqvolume, hqidegree, hqizero, hqleft, hqright, hforbidden,
      hmzero, hmlinear, hallowed, hauto, hmdegree, hmidegree, hjac, hconj, hnorm⟩ := hQ.2 k hk
    have hJdet : (J k).det ≠ 0 := isUnit_iff_ne_zero.1 ((Matrix.isUnit_iff_isUnit_det _).1 (hJ k hk))
    simpa only [assembledModel, assembledInverseModel, hk, ite_true] using
      automorphism_comp (linearPoly_automorphism (J k) hJdet) hauto
  · simpa only [assembledModel, assembledInverseModel, hk, ite_false] using hR k

theorem assembled_model_fixesZero
    {Fhat : ℕ → ComplexVector n → ComplexVector n} {Djet Jjet J : ℕ → Herm n}
    {w : ℕ → Fin n → ℝ} {active : ℕ → Prop} {Dstar : ℕ} {s : ℕ → ℝ}
    {C : ℝ} {qsol : JetData n} {R : ℕ → PolyMap n}
    (hQ : RegularJetSolution Fhat Djet Jjet w active d Dstar s C qsol)
    (hR : ∀ k, (R k).FixesZero) :
    ∀ k, (assembledModel active J qsol R k).FixesZero := by
  intro k
  by_cases hk : active k
  · obtain ⟨hqlin, hqdegree, hqvolume, hqidegree, hqizero, hqleft, hqright, hforbidden,
      hmzero, hmlinear, hallowed, hauto, hmdegree, hmidegree, hjac, hconj, hnorm⟩ := hQ.2 k hk
    simpa only [assembledModel, hk, ite_true] using comp_fixesZero (linearPoly_fixesZero (J k)) hmzero
  · simpa only [assembledModel, hk, ite_false] using hR k

theorem assembled_models_degree
    {Fhat : ℕ → ComplexVector n → ComplexVector n} {Djet Jjet J : ℕ → Herm n}
    {w : ℕ → Fin n → ℝ} {active : ℕ → Prop} {Dstar Dd : ℕ} {s : ℕ → ℝ}
    {C : ℝ} {qsol : JetData n} {R Rinv : ℕ → PolyMap n}
    (hQ : RegularJetSolution Fhat Djet Jjet w active d Dstar s C qsol)
    (hR : ∀ k, (R k).degree ≤ Dd ∧ (Rinv k).degree ≤ Dd) :
    ∀ k, (assembledModel active J qsol R k).degree ≤ max Dd Dstar ∧
      (assembledInverseModel active J qsol Rinv k).degree ≤ max Dd Dstar := by
  intro k
  by_cases hk : active k
  · obtain ⟨hqlin, hqdegree, hqvolume, hqidegree, hqizero, hqleft, hqright, hforbidden,
      hmzero, hmlinear, hallowed, hauto, hmdegree, hmidegree, hjac, hconj, hnorm⟩ := hQ.2 k hk
    have hG : ((linearPoly (J k)).comp (qsol.model k)).degree ≤ Dstar := by
      apply (comp_degree_le _ _).trans
      simpa only [one_mul] using (Nat.mul_le_mul (linearPoly_degree_le (J k)) hmdegree)
    have hI : ((qsol.inverseModel k).comp (linearPoly (J k)⁻¹)).degree ≤ Dstar := by
      apply (comp_degree_le _ _).trans
      simpa only [mul_one] using (Nat.mul_le_mul hmidegree (linearPoly_degree_le (J k)⁻¹))
    simpa only [assembledModel, assembledInverseModel, hk, ite_true] using
      And.intro (hG.trans (le_max_right _ _)) (hI.trans (le_max_right _ _))
  · simpa only [assembledModel, assembledInverseModel, hk, ite_false] using
      And.intro ((hR k).1.trans (le_max_left _ _)) ((hR k).2.trans (le_max_left _ _))

end Yau.Proofs.Y01Aux
