import Yau.Proofs.F01ANativeFiniteJetScalar

/-! A fixed compact base cylinder, finite spatial-jet box and positive matrix
lower bound give a compact range inside the computed native clock domain. -/
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology Matrix ComplexOrder Matrix.Norms.Frobenius

namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic
open Yau.LeafProofs.L17BootstrapClosedSlabAux
open Yau.LeafProofs.L17BootstrapEvolutionJetsAux
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

def nativeScalarFiniteJetRange (S : Point n → Matrix (Fin n) (Fin n) ℂ)
    (r : ℕ) (Kbase : Set (Point n)) (ell R : ℝ) :
    Set (Point n × FiniteTaylorJet (Space n) ℝ (r + 2)) :=
  (Kbase ×ˢ closedBall 0 R) ∩
    {p | (nativeFiniteClockMatrix S
      (projectBaseState (Space n) r (nativeFiniteSpatialStateCLM r p)) -
        (ell : ℂ) • 1).PosSemidef}

theorem nativeScalarFiniteJetRange_isCompact
    (S : Point n → Matrix (Fin n) (Fin n) ℂ) {Ω : Set (Point n)}
    (hS : ContDiffOn ℝ ∞ S Ω) (r : ℕ) {Kbase : Set (Point n)}
    (hKbase : IsCompact Kbase) (hKΩ : Kbase ⊆ Ω) (ell R : ℝ) :
    IsCompact (nativeScalarFiniteJetRange S r Kbase ell R) := by
  letI jetGroups : (j : Fin (r + 2 + 1)) → NormedAddCommGroup
      (ContinuousMultilinearMap ℝ (fun _ : Fin j.val => Space n) ℝ) :=
    fun j => ContinuousMultilinearMap.normedAddCommGroup'
  letI jetSpaces : (j : Fin (r + 2 + 1)) → NormedSpace ℝ
      (ContinuousMultilinearMap ℝ (fun _ : Fin j.val => Space n) ℝ) :=
    fun j => ContinuousMultilinearMap.normedSpace'
  letI jetFinite : (j : Fin (r + 2 + 1)) → FiniteDimensional ℝ
      (ContinuousMultilinearMap ℝ (fun _ : Fin j.val => Space n) ℝ) :=
    fun j => continuousMultilinearMap_finiteDimensional j.val
  letI : FiniteDimensional ℝ (FiniteTaylorJet (Space n) ℝ (r + 2)) :=
    Module.Finite.pi (h := jetFinite)
  letI : ProperSpace (FiniteTaylorJet (Space n) ℝ (r + 2)) := FiniteDimensional.proper ℝ _
  let Kbox : Set (Point n × FiniteTaylorJet (Space n) ℝ (r + 2)) := Kbase ×ˢ closedBall 0 R
  have hBox : IsCompact Kbox := hKbase.prod (isCompact_closedBall _ R)
  have hMatrix : ContinuousOn
      (fun p => nativeFiniteClockMatrix S
        (projectBaseState (Space n) r (nativeFiniteSpatialStateCLM r p))) Kbox :=
    (nativeFiniteClockMatrix_contDiffOn S hS).continuousOn.comp
      (((projectBaseState (Space n) r).comp (nativeFiniteSpatialStateCLM r)).continuous.continuousOn)
      (fun p hp => hKΩ hp.1)
  have hClosed := (hMatrix.sub (continuousOn_const
    (c := (ell : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)))).preimage_isClosed_of_isClosed
    hBox.isClosed Matrix.posSemidef_is_closed
  exact hBox.of_isClosed_subset hClosed inter_subset_left

theorem nativeScalarFiniteJetRange_subset_domain
    (S : Point n → Matrix (Fin n) (Fin n) ℂ) {Ω : Set (Point n)}
    (r : ℕ) {Kbase : Set (Point n)} (hKΩ : Kbase ⊆ Ω) {ell R : ℝ} (hell : 0 < ell) :
    nativeFiniteSpatialStateCLM r '' nativeScalarFiniteJetRange S r Kbase ell R ⊆
      prolongDomain (nativeFiniteClockDomain S Ω) r := by
  rintro s ⟨p, hp, rfl⟩
  refine ⟨hKΩ hp.1.1, ?_⟩
  have hBase : ((ell : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).PosDef :=
    Matrix.PosDef.one.smul (Complex.zero_lt_real.mpr hell)
  have hPos := hBase.add_posSemidef hp.2
  have hEq : (ell : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) +
      (nativeFiniteClockMatrix S
        (projectBaseState (Space n) r (nativeFiniteSpatialStateCLM r p)) - (ell : ℂ) • 1) =
      nativeFiniteClockMatrix S
        (projectBaseState (Space n) r (nativeFiniteSpatialStateCLM r p)) := by abel
  rw [hEq] at hPos
  exact (Complex.pos_iff.mp hPos.det_pos).1

theorem nativeScalarFiniteJetRange_actual_mem
    (S : Point n → Matrix (Fin n) (Fin n) ℂ) (f : Point n → ℝ)
    (r : ℕ) {Kbase : Set (Point n)} {ell R : ℝ} (hR : 0 ≤ R) (p : Point n)
    (hp : p ∈ Kbase) (hf : ContDiffAt ℝ 2 (fun z => f (z, p.2)) p.1)
    (hJets : ∀ j : Fin (r + 2 + 1), ‖iteratedFDeriv ℝ j.val (fun z => f (z, p.2)) p.1‖ ≤ R)
    (hLower : (S p + leviC (fun z => f (z, p.2)) p.1 -
      (ell : ℂ) • 1).PosSemidef) :
    (p, fun j : Fin (r + 2 + 1) => iteratedFDeriv ℝ j.val (fun z => f (z, p.2)) p.1) ∈
      nativeScalarFiniteJetRange S r Kbase ell R := by
  refine ⟨⟨hp, ?_⟩, ?_⟩
  · simpa only [mem_closedBall, dist_zero_right] using (pi_norm_le_iff_of_nonneg hR).mpr hJets
  · simp only [mem_setOf_eq]
    rw [nativeFiniteSpatialStateCLM_actual, projectBaseState_stateJ,
      nativeFiniteClockMatrix_actual S f p hf]
    exact hLower

end Yau.NodeProofs.F01Aux
