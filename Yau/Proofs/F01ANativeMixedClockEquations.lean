import Yau.Proofs.F01ANativeFiniteJetScalar
import Yau.Proofs.F01ANativeFiniteJetRange
import Yau.Proofs.F01AClosedMixedJetRecursion
import Yau.Proofs.F01AQuantitativeJointJets
import Yau.Proofs.F01PotentialClockRHS
import Yau.Proofs.F01SlabSpatialTensorClock

/-! The actual local potential equation supplies every input to the
quantitative mixed-clock recursion. Spatial estimates are its only
quantitative derivative input. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix ComplexOrder Matrix.Norms.Frobenius

namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic
open Yau.LeafProofs.L17BootstrapClosedSlabAux
open Yau.LeafProofs.L17BootstrapEvolutionJetsAux
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

theorem native_spatial_state_mapsTo_finite_clock_domain
    (S : Point n → Matrix (Fin n) (Fin n) ℂ) (f : Point n → ℝ)
    {O : Set (Space n)} (hO : IsOpen O) {T : ℝ} {Ω : Set (Point n)}
    (hBase : O ×ˢ Icc 0 T ⊆ Ω) (hf : ContDiffOn ℝ ∞ f (O ×ˢ Icc 0 T))
    (hPos : ∀ p ∈ O ×ˢ Icc 0 T,
      0 < (S p + leviC (fun z => f (z, p.2)) p.1).det.re) :
    MapsTo (stateJ (nativeSpatialJet f) 0) (O ×ˢ Icc 0 T) (nativeFiniteClockDomain S Ω) := by
  intro p hp
  refine ⟨hBase hp, ?_⟩
  rw [nativeFiniteClockMatrix_actual S f p
    (((contDiffOn_space_slice hf hp.2).contDiffAt (hO.mem_nhds hp.1)).of_le (by simp))]
  exact hPos p hp

/-- The original scalar logdet equation gives the actual clock derivative
of every spatial state component, as a specified finite-jet expression. -/
theorem native_spatial_clock_eq_prolong
    (S : Point n → Matrix (Fin n) (Fin n) ℂ) (b f : Point n → ℝ)
    {O : Set (Space n)} (hO : IsOpen O) {T : ℝ} (hT : 0 < T)
    {Ω : Set (Point n)} (hΩ : IsOpen Ω)
    (hS : ContDiffOn ℝ ∞ S Ω) (hb : ContDiffOn ℝ ∞ b Ω)
    (hBase : O ×ˢ Icc 0 T ⊆ Ω) (hf : ContDiffOn ℝ ∞ f (O ×ˢ Icc 0 T))
    (hPos : ∀ p ∈ O ×ˢ Icc 0 T,
      0 < (S p + leviC (fun z => f (z, p.2)) p.1).det.re)
    (hPDE : ∀ x ∈ O, ∀ t ∈ Icc 0 T, HasDerivWithinAt (fun s => f (x, s))
      (localPotentialClockRHS S b f (x, t)) (Icc 0 T) t) :
    ∀ j p, p ∈ O ×ˢ Icc 0 T →
      HasDerivWithinAt (fun t => nativeSpatialJet f j (p.1, t))
        (prolong (nativeFiniteClockScalar S b) j (stateJ (nativeSpatialJet f) j p))
        (Icc 0 T) p.2 := by
  let P := localPotentialClockRHS S b f
  have hFS (t : ℝ) (ht : t ∈ Icc 0 T) : ContDiffOn ℝ ∞ (fun z => f (z, t)) O :=
    contDiffOn_space_slice hf ht
  have hPS (t : ℝ) (ht : t ∈ Icc 0 T) : ContDiffOn ℝ ∞ (fun z => P (z, t)) O := by
    apply localPotentialClockRHS_smooth_slice S b f hO t
    · exact hS.comp (contDiffOn_id.prodMk contDiffOn_const) (fun z hz => hBase ⟨hz, ht⟩)
    · exact hb.comp (contDiffOn_id.prodMk contDiffOn_const) (fun z hz => hBase ⟨hz, ht⟩)
    · exact hFS t ht
    · exact fun z hz => hPos (z, t) ⟨hz, ht⟩
  have hSpaceJ : ∀ j z, z ∈ O → ∀ t, t ∈ Icc 0 T →
      HasFDerivAt (fun y => nativeSpatialJet f j (y, t)) (nativeSpatialJet f (j + 1) (z, t)) z :=
    fun j z hz t ht => nativeSpatialJet_hasFDerivAt f j (z, t)
      ((hFS t ht).contDiffAt (hO.mem_nhds hz))
  have hSpaceP : ∀ j z, z ∈ O → ∀ t, t ∈ Icc 0 T →
      HasFDerivAt (fun y => nativeSpatialJet P j (y, t)) (nativeSpatialJet P (j + 1) (z, t)) z :=
    fun j z hz t ht => nativeSpatialJet_hasFDerivAt P j (z, t)
      ((hPS t ht).contDiffAt (hO.mem_nhds hz))
  have hState := native_spatial_state_mapsTo_finite_clock_domain S f hO hBase hf hPos
  have hEquation : ∀ p ∈ O ×ˢ Icc 0 T,
      nativeSpatialJet P 0 p = nativeFiniteClockScalar S b (stateJ (nativeSpatialJet f) 0 p) := by
    intro p hp
    rw [nativeSpatialJet_zero, nativeFiniteClockScalar_actual S b f p
      (((hFS p.2 hp.2).contDiffAt (hO.mem_nhds hp.1)).of_le (by simp))]
    rfl
  have hProlong := timeJet_eq_prolong hO hSpaceJ hSpaceP
    (nativeFiniteClockDomain_isOpen S hΩ hS) (nativeFiniteClockScalar_contDiffOn S b hS hb)
    hState hEquation
  have hDense : ∀ t ∈ Icc (0 : ℝ) T, t ∈ closure (interior (Icc 0 T)) := by
    intro t ht
    rw [interior_Icc, closure_Ioo hT.ne]
    exact ht
  intro j p hp
  have hClock := nativeSpatialJet_hasDerivWithinAt_of_tensor_clock f P j p
    (slab_spatial_tensor_time_jet hO (uniqueDiffOn_Icc hT) hDense hf hPS hPDE j hp.1 hp.2)
  exact hClock.congr_deriv (hProlong j p hp)

/-- An actual family of local native potential solutions has uniform closed
mixed-jet budgets from one compact range of its spatial tensor states. -/
theorem local_uniform_mixed_jet_budgets
    {ι : Type*} (S : Point n → Matrix (Fin n) (Fin n) ℂ) (b : Point n → ℝ)
    (f : ι → Point n → ℝ) {O : Set (Space n)} (hO : IsOpen O) {T : ℝ} (hT : 0 < T)
    {Ω : Set (Point n)} (hΩ : IsOpen Ω)
    (hS : ContDiffOn ℝ ∞ S Ω) (hb : ContDiffOn ℝ ∞ b Ω)
    (hBase : O ×ˢ Icc 0 T ⊆ Ω) (hf : ∀ i, ContDiffOn ℝ ∞ (f i) (O ×ˢ Icc 0 T))
    (hPos : ∀ i p, p ∈ O ×ˢ Icc 0 T →
      0 < (S p + leviC (fun z => f i (z, p.2)) p.1).det.re)
    (hPDE : ∀ i x, x ∈ O → ∀ t, t ∈ Icc 0 T → HasDerivWithinAt (fun s => f i (x, s))
      (localPotentialClockRHS S b (f i) (x, t)) (Icc 0 T) t)
    (a c : ℕ) {Q : Set (Point n)} (hQ : Q ⊆ O ×ˢ Icc 0 T)
    {K : Set (Point n × FiniteTaylorJet (Space n) ℝ (mixedClockJetOrder a c + 2))}
    (hK : IsCompact K)
    (hKD : nativeFiniteSpatialStateCLM (mixedClockJetOrder a c) '' K ⊆
      prolongDomain (nativeFiniteClockDomain S Ω) (mixedClockJetOrder a c))
    (hRange : ∀ i p, p ∈ Q →
      (p, fun j : Fin (mixedClockJetOrder a c + 2 + 1) =>
        iteratedFDeriv ℝ j.val (fun z => f i (z, p.2)) p.1) ∈ K) :
    ∃ B : ℝ, 0 < B ∧ ∀ i p, p ∈ Q →
      ‖iteratedDerivWithin a (fun t => nativeSpatialJet (f i) c (p.1, t)) (Icc 0 T) p.2‖ ≤ B := by
  apply actual_closed_mixed_clock_jets_uniformly_bounded
    (fun i => nativeSpatialJet (f i)) (nativeFiniteClockScalar S b) (uniqueDiffOn_Icc hT)
    (nativeFiniteClockDomain_isOpen S hΩ hS) (nativeFiniteClockScalar_contDiffOn S b hS hb)
    (fun i => native_spatial_state_mapsTo_finite_clock_domain S (f i) hO hBase (hf i) (hPos i))
    (fun i => native_spatial_clock_eq_prolong S b (f i) hO hT hΩ hS hb hBase (hf i) (hPos i) (hPDE i))
    a c hQ (hK.image (nativeFiniteSpatialStateCLM _).continuous) hKD
  intro i p hp
  exact ⟨_, hRange i p hp, nativeFiniteSpatialStateCLM_actual (f i) _ p⟩

/-- The actual finite-jet potential clock produces a uniform bound for every
genuine joint Fréchet tensor on the original closed slab. -/
theorem local_uniform_joint_jet_budgets
    {ι : Type*} (S : Point n → Matrix (Fin n) (Fin n) ℂ) (b : Point n → ℝ)
    (f : ι → Point n → ℝ) {O : Set (Space n)} (hO : IsOpen O) (hConv : Convex ℝ O)
    {T : ℝ} (hT : 0 < T) {Ω : Set (Point n)} (hΩ : IsOpen Ω)
    (hS : ContDiffOn ℝ ∞ S Ω) (hb : ContDiffOn ℝ ∞ b Ω)
    (hBase : O ×ˢ Icc 0 T ⊆ Ω) (hf : ∀ i, ContDiffOn ℝ ∞ (f i) (O ×ˢ Icc 0 T))
    (hPos : ∀ i p, p ∈ O ×ˢ Icc 0 T →
      0 < (S p + leviC (fun z => f i (z, p.2)) p.1).det.re)
    (hPDE : ∀ i x, x ∈ O → ∀ t, t ∈ Icc 0 T → HasDerivWithinAt (fun s => f i (x, s))
      (localPotentialClockRHS S b (f i) (x, t)) (Icc 0 T) t)
    (k : ℕ) {Q : Set (Point n)} (hQ : Q ⊆ O ×ˢ Icc 0 T)
    {K : Set (Point n × FiniteTaylorJet (Space n) ℝ (mixedClockJetOrder k 0 + 2))}
    (hK : IsCompact K)
    (hKD : nativeFiniteSpatialStateCLM (mixedClockJetOrder k 0) '' K ⊆
      prolongDomain (nativeFiniteClockDomain S Ω) (mixedClockJetOrder k 0))
    (hRange : ∀ i p, p ∈ Q →
      (p, fun j : Fin (mixedClockJetOrder k 0 + 2 + 1) =>
        iteratedFDeriv ℝ j.val (fun z => f i (z, p.2)) p.1) ∈ K) :
    ∃ B : ℝ, 0 < B ∧ ∀ i p, p ∈ Q →
      ‖iteratedFDerivWithin ℝ k (f i) (O ×ˢ Icc 0 T) p‖ ≤ B := by
  have hCont (i : ι) (j : ℕ) : ContinuousOn (nativeSpatialJet (f i) j) (O ×ˢ Icc 0 T) :=
    (nativeSpatialJet_contDiffOn j (slab_spatial_tensor_smooth hO (uniqueDiffOn_Icc hT) (hf i) j)).continuousOn
  have hSpace (i : ι) (j : ℕ) (z : Space n) (hz : z ∈ O) (t : ℝ) (ht : t ∈ Icc 0 T) :
      HasFDerivAt (fun y => nativeSpatialJet (f i) j (y, t))
        (nativeSpatialJet (f i) (j + 1) (z, t)) z :=
    nativeSpatialJet_hasFDerivAt (f i) j (z, t)
      ((contDiffOn_space_slice (hf i) ht).contDiffAt (hO.mem_nhds hz))
  have hZero (i : ι) : nativeSpatialJet (f i) 0 = f i :=
    funext (fun p => nativeSpatialJet_zero (f i) p)
  obtain ⟨B, hB, hBound⟩ := actual_joint_clock_jets_uniformly_bounded
    (fun i => nativeSpatialJet (f i)) (nativeFiniteClockScalar S b) hO hConv hT
    (nativeFiniteClockDomain_isOpen S hΩ hS) (nativeFiniteClockScalar_contDiffOn S b hS hb)
    (fun i => native_spatial_state_mapsTo_finite_clock_domain S (f i) hO hBase (hf i) (hPos i))
    (fun i => by rw [hZero]; exact hf i) hCont hSpace
    (fun i => native_spatial_clock_eq_prolong S b (f i) hO hT hΩ hS hb hBase (hf i) (hPos i) (hPDE i))
    k hQ (hK.image (nativeFiniteSpatialStateCLM _).continuous) hKD
    (fun i p hp => ⟨_, hRange i p hp, nativeFiniteSpatialStateCLM_actual (f i) _ p⟩)
  exact ⟨B, hB, fun i p hp => by simpa only [hZero i] using hBound i p hp⟩

/-- The direct quantitative adapter takes actual spatial derivative budgets,
a compact base cylinder and a positive matrix lower bound. It constructs the
compact positive finite-jet range itself. -/
theorem local_uniform_joint_jet_budgets_of_spatial_bounds
    {ι : Type*} (S : Point n → Matrix (Fin n) (Fin n) ℂ) (b : Point n → ℝ)
    (f : ι → Point n → ℝ) {O : Set (Space n)} (hO : IsOpen O) (hConv : Convex ℝ O)
    {T : ℝ} (hT : 0 < T) {Ω : Set (Point n)} (hΩ : IsOpen Ω)
    (hS : ContDiffOn ℝ ∞ S Ω) (hb : ContDiffOn ℝ ∞ b Ω)
    (hBase : O ×ˢ Icc 0 T ⊆ Ω) (hf : ∀ i, ContDiffOn ℝ ∞ (f i) (O ×ˢ Icc 0 T))
    (hPos : ∀ i p, p ∈ O ×ˢ Icc 0 T →
      0 < (S p + leviC (fun z => f i (z, p.2)) p.1).det.re)
    (hPDE : ∀ i x, x ∈ O → ∀ t, t ∈ Icc 0 T → HasDerivWithinAt (fun s => f i (x, s))
      (localPotentialClockRHS S b (f i) (x, t)) (Icc 0 T) t)
    (k : ℕ) {Q Kbase : Set (Point n)} (hQ : Q ⊆ O ×ˢ Icc 0 T)
    (hKbase : IsCompact Kbase) (hKΩ : Kbase ⊆ Ω) (hQbase : Q ⊆ Kbase)
    {ell R : ℝ} (hell : 0 < ell) (hR : 0 ≤ R)
    (hJets : ∀ i p, p ∈ Q → ∀ j : Fin (mixedClockJetOrder k 0 + 2 + 1),
      ‖iteratedFDeriv ℝ j.val (fun z => f i (z, p.2)) p.1‖ ≤ R)
    (hLower : ∀ i p, p ∈ Q →
      (S p + leviC (fun z => f i (z, p.2)) p.1 - (ell : ℂ) • 1).PosSemidef) :
    ∃ B : ℝ, 0 < B ∧ ∀ i p, p ∈ Q →
      ‖iteratedFDerivWithin ℝ k (f i) (O ×ˢ Icc 0 T) p‖ ≤ B := by
  apply local_uniform_joint_jet_budgets S b f hO hConv hT hΩ hS hb hBase hf hPos hPDE k hQ
    (nativeScalarFiniteJetRange_isCompact S hS _ hKbase hKΩ ell R)
    (nativeScalarFiniteJetRange_subset_domain S _ hKΩ hell)
  intro i p hp
  exact nativeScalarFiniteJetRange_actual_mem S (f i) _ hR p (hQbase hp)
    (((contDiffOn_space_slice (hf i) (hQ hp).2).contDiffAt (hO.mem_nhds (hQ hp).1)).of_le (by simp))
    (hJets i p hp) (hLower i p hp)

end Yau.NodeProofs.F01Aux
