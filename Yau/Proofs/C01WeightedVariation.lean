import Yau.Proofs.C01IndexCutoffJets
import Yau.Proofs.C01FamilyPathEnergy

/-! A smooth endpoint cutoff gives an actual variation on one open
neighborhood of the whole compact unit interval. -/

noncomputable section
open Filter
open scoped Topology ContDiff Manifold

namespace Yau.NodeProofs.C01Aux
open Yau Yau.Blueprint Yau.LeafProofs.L12Aux

theorem exists_weightedVariation_domain
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (ψ : ℝ → ℝ) (hψ : Continuous ψ)
    (J : Set ℝ) (U : Set V) (hJ : IsOpen J) (hU : IsOpen U)
    (hunit : Set.Icc (0 : ℝ) 1 ⊆ J) (hzero : (0 : V) ∈ U) :
    ∃ J' U', IsOpen J' ∧ IsOpen U' ∧ Set.Icc (0 : ℝ) 1 ⊆ J' ∧
      (0 : V) ∈ U' ∧
      Set.MapsTo (fun p : ℝ × V => (p.1, ψ p.1 • p.2)) (J' ×ˢ U') (J ×ˢ U) := by
  let F : ℝ × V → ℝ × V := fun p => (p.1, ψ p.1 • p.2)
  have hF : Continuous F := continuous_fst.prodMk ((hψ.comp continuous_fst).smul continuous_snd)
  have hW : IsOpen (F ⁻¹' (J ×ˢ U)) := (hJ.prod hU).preimage hF
  have hbase : Set.Icc (0 : ℝ) 1 ×ˢ ({0} : Set V) ⊆ F ⁻¹' (J ×ˢ U) := by
    rintro p ⟨hp, hz⟩
    have hp0 : p.2 = 0 := Set.mem_singleton_iff.mp hz
    exact ⟨hunit hp, by simpa only [F, hp0, smul_zero] using hzero⟩
  obtain ⟨J', U', hJ', hU', hsub, hzero', hprod⟩ :=
    generalized_tube_lemma isCompact_Icc isCompact_singleton hW hbase
  exact ⟨J', U', hJ', hU', hsub, hzero' (Set.mem_singleton 0), hprod⟩

variable {n : ℕ} {M : ComplexManifold n}

def weightedVariation (A : ℝ → ComplexVector n → M.Carrier) (ψ : ℝ → ℝ)
    (u : ℝ) (v : ComplexVector n) : M.Carrier := A u (ψ u • v)

theorem weightedVariation_contMDiffOn
    (A : ℝ → ComplexVector n → M.Carrier) (ψ : ℝ → ℝ)
    (hψ : ContDiff ℝ 3 ψ) (J J' : Set ℝ) (U U' : Set (ComplexVector n))
    (hmap : Set.MapsTo (fun p : ℝ × ComplexVector n => (p.1, ψ p.1 • p.2))
      (J' ×ˢ U') (J ×ˢ U)) :
    letI := manifold_realSmooth M
    ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ComplexVector n)) 𝓘(ℝ, ComplexVector n) 3
      (Function.uncurry A) (J ×ˢ U) →
    ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ComplexVector n)) 𝓘(ℝ, ComplexVector n) 3
      (Function.uncurry (weightedVariation A ψ)) (J' ×ˢ U') := by
  letI := manifold_realSmooth M
  intro hA
  have hψF : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ComplexVector n)) 𝓘(ℝ, ℝ) 3
      (fun p : ℝ × ComplexVector n => ψ p.1) := hψ.contMDiff.comp contMDiff_fst
  have hsm : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ComplexVector n)) 𝓘(ℝ, ComplexVector n) 3
      (fun p : ℝ × ComplexVector n => ψ p.1 • p.2) := hψF.smul contMDiff_snd
  exact hA.comp (contMDiff_fst.prodMk hsm).contMDiffOn hmap

theorem weightedVariation_endpoints
    (A : ℝ → ComplexVector n → M.Carrier) (ψ : ℝ → ℝ) (q y : M.Carrier)
    (hψ0 : ψ 0 = 0) (hψ1 : ψ 1 = 0) (hA0 : A 0 0 = q) (hA1 : A 1 0 = y)
    (v : ComplexVector n) :
    weightedVariation A ψ 0 v = q ∧ weightedVariation A ψ 1 v = y := by
  simp only [weightedVariation, hψ0, hψ1, zero_smul, hA0, hA1, and_self]

theorem weightedVariation_ray
    (A : ℝ → ComplexVector n → M.Carrier) (ψ : ℝ → ℝ)
    (u r : ℝ) (w : ComplexVector n) :
    weightedVariation A ψ u (r • w) = A u (r • (ψ u • w)) := by
  simp only [weightedVariation, smul_smul]
  rw [mul_comm (ψ u) r]

end Yau.NodeProofs.C01Aux
