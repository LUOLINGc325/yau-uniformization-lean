import Yau.Proofs.F01ANativeSpatialJetTower
import Yau.Proofs.F01AClosedMixedJetRecursion

/-! The same finite spatial state computes the full genuine joint tensor,
including both closed faces. This supplies joint operator-norm budgets
without a separate mixed-word or permutation bound. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace Yau.NodeProofs.F01Aux
open Yau.LeafProofs.L17BootstrapClosedSlabAux
open Yau.LeafProofs.L17BootstrapEvolutionJetsAux
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem norm_clm_comp_of_norm_preserving
    {V W Z : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (L : W →L[ℝ] Z) (hL : ∀ w, ‖L w‖ = ‖w‖) (A : V →L[ℝ] W) :
    ‖L.comp A‖ = ‖A‖ := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro v
    rw [ContinuousLinearMap.comp_apply, hL]
    exact A.le_opNorm v
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro v
    rw [← hL (A v)]
    exact (L.comp A).le_opNorm v

theorem spatialTensorToNestedJet_norm (k : ℕ)
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin k => E) ℝ) :
    ‖spatialTensorToNestedJet k A‖ = ‖A‖ := by
  induction k with
  | zero => exact (continuousMultilinearCurryFin0 ℝ E ℝ).norm_map A
  | succ k ih =>
      change ‖(spatialTensorToNestedJet k).comp
        ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => E) ℝ) A)‖ = _
      rw [norm_clm_comp_of_norm_preserving _ ih]
      exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => E) ℝ).norm_map A

def finiteStateJointDirection (F : State E 0 → ℝ) (r : ℕ) (s : State E (r + 2)) :
    (E × ℝ) →L[ℝ] State E r :=
  productDerivativeCLM E (State E r)
    (spatialDirection E r (clockRestrictState (Nat.le_succ (r + 1)) s),
      finiteClockTimeDirection F r s)

theorem finiteStateJointDirection_contDiffOn {F : State E 0 → ℝ} {D : Set (State E 0)}
    (hD : IsOpen D) (hF : ContDiffOn ℝ ∞ F D) (r : ℕ) :
    ContDiffOn ℝ ∞ (finiteStateJointDirection F r) (prolongDomain D (r + 2)) := by
  apply (productDerivativeCLM E (State E r)).contDiff.comp_contDiffOn
  exact (((spatialDirection_contDiff E r).comp
    (clockRestrictState (E := E) (m := r + 1) (r := r + 2) (Nat.le_succ (r + 1))).contDiff).contDiffOn).prodMk
    (finiteClockTimeDirection_contDiffOn hD hF r)

def finiteJointClockJet (F : State E 0 → ℝ) :
    (k : ℕ) → State E (mixedClockJetOrder k 0) → Jet (E × ℝ) ℝ k
  | 0 => fun s => s.2 ⟨0, by simp only [mixedClockJetOrder]; omega⟩
  | k + 1 => fun s =>
      (fderiv ℝ (finiteJointClockJet F k)
        (clockRestrictState (Nat.le_add_right _ 2) s)).comp
        (finiteStateJointDirection F (mixedClockJetOrder k 0) s)

theorem finiteJointClockJet_contDiffOn {F : State E 0 → ℝ} {D : Set (State E 0)}
    (hD : IsOpen D) (hF : ContDiffOn ℝ ∞ F D) (k : ℕ) :
    ContDiffOn ℝ ∞ (finiteJointClockJet F k) (prolongDomain D (mixedClockJetOrder k 0)) := by
  induction k with
  | zero =>
      let L : State E 0 →L[ℝ] ℝ :=
        (ContinuousLinearMap.proj (⟨0, by decide⟩ : Fin 3)).comp
          (ContinuousLinearMap.snd ℝ (E × ℝ) (JetPack E 2))
      exact L.contDiff.contDiffOn
  | succ k ih =>
      have hd := ih.fderiv_of_isOpen (prolongDomain_isOpen hD _) (m := ∞) (by simp)
      exact (hd.comp
        (clockRestrictState (Nat.le_add_right (mixedClockJetOrder k 0) 2)).contDiff.contDiffOn
        (clockRestrictState_mapsTo D _)).clm_comp
        (finiteStateJointDirection_contDiffOn hD hF _)

theorem nested_joint_tensor_hasFDerivWithinAt
    {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : V → ℝ} {Q : Set V} (hQ : UniqueDiffOn ℝ Q) (hf : ContDiffOn ℝ ∞ f Q)
    (k : ℕ) {p : V} (hp : p ∈ Q) :
    HasFDerivWithinAt
      (fun q => spatialTensorToNestedJet k (iteratedFDerivWithin ℝ k f Q q))
      (spatialTensorToNestedJet (k + 1) (iteratedFDerivWithin ℝ (k + 1) f Q p)) Q p := by
  have hh := (hf.differentiableOn_iteratedFDerivWithin
    (ENat.natCast_lt_of_coe_top_le_withTop le_rfl k) hQ p hp).hasFDerivWithinAt
  rw [fderivWithin_iteratedFDerivWithin] at hh
  convert! (spatialTensorToNestedJet (E := V) k).hasFDerivAt.comp_hasFDerivWithinAt p hh using 1

variable [CompleteSpace E]

theorem finiteState_hasFDerivWithinAt_of_actual_clocks
    (J : (j : ℕ) → E × ℝ → Jet E ℝ j) (F : State E 0 → ℝ)
    {O : Set E} (hO : IsOpen O) (hConv : Convex ℝ O) {T : ℝ} (hT : 0 < T)
    {D : Set (State E 0)} (hD : IsOpen D) (hF : ContDiffOn ℝ ∞ F D)
    (hState : MapsTo (stateJ J 0) (O ×ˢ Icc 0 T) D)
    (hCont : ∀ j, ContinuousOn (J j) (O ×ˢ Icc 0 T))
    (hSpace : ∀ j z, z ∈ O → ∀ t, t ∈ Icc 0 T →
      HasFDerivAt (fun y => J j (y, t)) (J (j + 1) (z, t)) z)
    (hClock : ∀ j p, p ∈ O ×ˢ Icc 0 T → HasDerivWithinAt (fun t => J j (p.1, t))
      (prolong F j (stateJ J j p)) (Icc 0 T) p.2)
    (r : ℕ) {p : E × ℝ} (hp : p ∈ O ×ˢ Icc 0 T) :
    HasFDerivWithinAt (stateJ J r)
      (finiteStateJointDirection F r (stateJ J (r + 2) p)) (O ×ˢ Icc 0 T) p := by
  have hStateCont (m : ℕ) : ContinuousOn (stateJ J m) (O ×ˢ Icc 0 T) :=
    continuousOn_id.prodMk (continuousOn_pi.mpr (fun j => hCont j.val))
  have hA : ContinuousOn (fun q => spatialDirection E r (stateJ J (r + 1) q)) (O ×ˢ Icc 0 T) :=
    (spatialDirection_contDiff E r).continuous.comp_continuousOn (hStateCont (r + 1))
  have hB : ContinuousOn (fun q => finiteClockTimeDirection F r (stateJ J (r + 2) q))
      (O ×ˢ Icc 0 T) :=
    (finiteClockTimeDirection_contDiffOn hD hF r).continuousOn.comp (hStateCont (r + 2))
      (stateJ_mapsTo J hState (r + 2))
  have hh := hasFDerivWithinAt_of_spatial_time hO hConv hT (hStateCont r) hA hB
    (fun z hz t ht => stateJ_hasFDerivAt J hSpace r hz ht)
    (fun z hz t ht => finiteState_hasDerivWithinAt_of_clock J F (z, t)
      (fun j => hClock j (z, t) ⟨hz, ht⟩) r) hp.1 hp.2
  simpa only [finiteStateJointDirection, clockRestrictState_stateJ, productDerivativeCLM_apply] using hh

theorem finiteJointClockJet_actual
    (J : (j : ℕ) → E × ℝ → Jet E ℝ j) (F : State E 0 → ℝ)
    {O : Set E} (hO : IsOpen O) (hConv : Convex ℝ O) {T : ℝ} (hT : 0 < T)
    {D : Set (State E 0)} (hD : IsOpen D) (hF : ContDiffOn ℝ ∞ F D)
    (hState : MapsTo (stateJ J 0) (O ×ˢ Icc 0 T) D)
    (hf : ContDiffOn ℝ ∞ (J 0) (O ×ˢ Icc 0 T))
    (hCont : ∀ j, ContinuousOn (J j) (O ×ˢ Icc 0 T))
    (hSpace : ∀ j z, z ∈ O → ∀ t, t ∈ Icc 0 T →
      HasFDerivAt (fun y => J j (y, t)) (J (j + 1) (z, t)) z)
    (hClock : ∀ j p, p ∈ O ×ˢ Icc 0 T → HasDerivWithinAt (fun t => J j (p.1, t))
      (prolong F j (stateJ J j p)) (Icc 0 T) p.2)
    (k : ℕ) : ∀ p ∈ O ×ˢ Icc 0 T,
      spatialTensorToNestedJet k (iteratedFDerivWithin ℝ k (J 0) (O ×ˢ Icc 0 T) p) =
        finiteJointClockJet F k (stateJ J (mixedClockJetOrder k 0) p) := by
  have hQ := hO.uniqueDiffOn.prod (uniqueDiffOn_Icc hT)
  induction k with
  | zero =>
      intro p hp
      change (continuousMultilinearCurryFin0 ℝ (E × ℝ) ℝ)
        (iteratedFDerivWithin ℝ 0 (J 0) (O ×ˢ Icc 0 T) p) = _
      rw [continuousMultilinearCurryFin0_apply, iteratedFDerivWithin_zero_apply]
      rfl
  | succ k ih =>
      intro p hp
      have hMem : stateJ J (mixedClockJetOrder k 0) p ∈
          prolongDomain D (mixedClockJetOrder k 0) := hState hp
      have hDiff := ((finiteJointClockJet_contDiffOn hD hF k).contDiffAt
        ((prolongDomain_isOpen hD _).mem_nhds hMem)).differentiableAt (by simp)
      have hRight := hDiff.hasFDerivAt.comp_hasFDerivWithinAt p
        (finiteState_hasFDerivWithinAt_of_actual_clocks J F hO hConv hT hD hF hState
          hCont hSpace hClock (mixedClockJetOrder k 0) hp)
      have hActual := hRight.congr' (fun q hq => ih q hq) hp
      exact hQ.eq hp (nested_joint_tensor_hasFDerivWithinAt hQ hf k hp) hActual

theorem actual_joint_clock_jets_uniformly_bounded
    {ι : Type*} (J : ι → (j : ℕ) → E × ℝ → Jet E ℝ j)
    (F : State E 0 → ℝ) {O : Set E} (hO : IsOpen O) (hConv : Convex ℝ O)
    {T : ℝ} (hT : 0 < T) {D : Set (State E 0)} (hD : IsOpen D)
    (hF : ContDiffOn ℝ ∞ F D)
    (hState : ∀ i, MapsTo (stateJ (J i) 0) (O ×ˢ Icc 0 T) D)
    (hf : ∀ i, ContDiffOn ℝ ∞ (J i 0) (O ×ˢ Icc 0 T))
    (hCont : ∀ i j, ContinuousOn (J i j) (O ×ˢ Icc 0 T))
    (hSpace : ∀ i j z, z ∈ O → ∀ t, t ∈ Icc 0 T →
      HasFDerivAt (fun y => J i j (y, t)) (J i (j + 1) (z, t)) z)
    (hClock : ∀ i j p, p ∈ O ×ˢ Icc 0 T → HasDerivWithinAt (fun t => J i j (p.1, t))
      (prolong F j (stateJ (J i) j p)) (Icc 0 T) p.2)
    (k : ℕ) {Q : Set (E × ℝ)} (hQ : Q ⊆ O ×ˢ Icc 0 T)
    {K : Set (State E (mixedClockJetOrder k 0))} (hK : IsCompact K)
    (hKD : K ⊆ prolongDomain D (mixedClockJetOrder k 0))
    (hRange : ∀ i p, p ∈ Q → stateJ (J i) (mixedClockJetOrder k 0) p ∈ K) :
    ∃ B : ℝ, 0 < B ∧ ∀ i p, p ∈ Q →
      ‖iteratedFDerivWithin ℝ k (J i 0) (O ×ˢ Icc 0 T) p‖ ≤ B := by
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn
    ((finiteJointClockJet_contDiffOn hD hF k).continuousOn.mono hKD)
  refine ⟨max 1 B + 1, by positivity, ?_⟩
  intro i p hp
  calc
    _ = ‖spatialTensorToNestedJet k
        (iteratedFDerivWithin ℝ k (J i 0) (O ×ˢ Icc 0 T) p)‖ :=
      (spatialTensorToNestedJet_norm (E := E × ℝ) k _).symm
    _ = ‖finiteJointClockJet F k (stateJ (J i) (mixedClockJetOrder k 0) p)‖ :=
      congrArg norm (finiteJointClockJet_actual (J i) F hO hConv hT hD hF (hState i) (hf i)
        (hCont i) (hSpace i) (hClock i) k p (hQ hp))
    _ ≤ _ := (hB _ (hRange i p hp)).trans (by linarith [le_max_right (1 : ℝ) B])

end Yau.NodeProofs.F01Aux
