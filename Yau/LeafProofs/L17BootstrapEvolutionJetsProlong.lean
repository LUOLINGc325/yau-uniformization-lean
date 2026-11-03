import Yau.LeafProofs.L17BootstrapEvolutionJetsState

open Set Filter
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17BootstrapEvolutionJetsAux
open L17BootstrapClosedSlabAux
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

def prolong (F : State E 0 → ℝ) : (k : ℕ) → State E k → Jet E ℝ k
  | 0 => F
  | k+1 => fun s => (fderiv ℝ (prolong F k) (truncateState E k s)).comp
      (spatialDirection E k s)

def prolongDomain (D : Set (State E 0)) (k : ℕ) : Set (State E k) :=
  (projectBaseState E k) ⁻¹' D

theorem prolongDomain_isOpen {D : Set (State E 0)} (hD : IsOpen D) (k : ℕ) :
    IsOpen (prolongDomain D k) := hD.preimage (projectBaseState E k).continuous

theorem truncateState_mapsTo (D : Set (State E 0)) (k : ℕ) :
    MapsTo (truncateState E k) (prolongDomain D (k+1)) (prolongDomain D k) := by
  intro s hs
  simpa only [prolongDomain,mem_preimage,projectBaseState_truncate] using hs

theorem prolong_contDiffOn {F : State E 0 → ℝ} {D : Set (State E 0)}
    (hD : IsOpen D) (hF : ContDiffOn ℝ ∞ F D) (k : ℕ) :
    ContDiffOn ℝ ∞ (prolong F k) (prolongDomain D k) := by
  induction k with
  | zero =>
      change ContDiffOn ℝ ∞ F (prolongDomain D 0)
      have heq : prolongDomain D 0=D := by
        ext s
        change projectBaseState E 0 s∈D ↔ s∈D
        rw [projectBaseState_zero]
      rw [heq]
      exact hF
  | succ k ih =>
      have hd := ih.fderiv_of_isOpen (prolongDomain_isOpen hD k)
        (show (∞ : ℕ∞ω)+1 ≤ ∞ by simp)
      exact (hd.comp (truncateState E k).contDiff.contDiffOn (truncateState_mapsTo D k)).clm_comp
        (spatialDirection_contDiff E k).contDiffOn

variable (J : (k : ℕ) → E × ℝ → Jet E ℝ k)

def stateJ (k : ℕ) (q : E × ℝ) : State E k := (q,fun j => J j.val q)

@[simp] theorem projectBaseState_stateJ (k : ℕ) (q : E × ℝ) :
    projectBaseState E k (stateJ J k q)=stateJ J 0 q := rfl

@[simp] theorem truncateState_stateJ (k : ℕ) (q : E × ℝ) :
    truncateState E k (stateJ J (k+1) q)=stateJ J k q := rfl

theorem stateJ_mapsTo {S : Set (E × ℝ)} {D : Set (State E 0)}
    (hState : MapsTo (stateJ J 0) S D) (k : ℕ) :
    MapsTo (stateJ J k) S (prolongDomain D k) := by
  intro q hq
  exact hState hq

theorem stateJ_contDiffOn {S : Set (E × ℝ)} {m : ℕ∞ω}
    (hJ : ∀ k, ContDiffOn ℝ m (J k) S) (k : ℕ) :
    ContDiffOn ℝ m (stateJ J k) S :=
  contDiffOn_id.prodMk (contDiffOn_pi.mpr fun j => hJ j.val)

theorem stateJ_hasFDerivAt {O : Set E} {T : ℝ}
    (hSpace : ∀ k z, z∈O → ∀ t, t∈Icc 0 T →
      HasFDerivAt (fun y => J k (y,t)) (J (k+1) (z,t)) z)
    (k : ℕ) {z : E} {t : ℝ} (hz : z∈O) (ht : t∈Icc 0 T) :
    HasFDerivAt (fun y => stateJ J k (y,t))
      (spatialDirection E k (stateJ J (k+1) (z,t))) z := by
  have hp : HasFDerivAt (fun y : E => (y,t)) (ContinuousLinearMap.inl ℝ E ℝ) z := by
    have heq : ((ContinuousLinearMap.id ℝ E).prod (0 : E →L[ℝ] ℝ))=
        ContinuousLinearMap.inl ℝ E ℝ := by ext a <;> rfl
    rw [←heq]
    exact (hasFDerivAt_id z).prodMk (hasFDerivAt_const t z)
  exact hp.prodMk (hasFDerivAt_pi.mpr fun j => hSpace j.val z hz t ht)

variable {J}

theorem timeJet_eq_prolong {O : Set E} (hO : IsOpen O) {T : ℝ}
    {B : (k : ℕ) → E × ℝ → Jet E ℝ k}
    (hSpaceJ : ∀ k z, z∈O → ∀ t, t∈Icc 0 T →
      HasFDerivAt (fun y => J k (y,t)) (J (k+1) (z,t)) z)
    (hSpaceB : ∀ k z, z∈O → ∀ t, t∈Icc 0 T →
      HasFDerivAt (fun y => B k (y,t)) (B (k+1) (z,t)) z)
    {F : State E 0 → ℝ} {D : Set (State E 0)}
    (hD : IsOpen D) (hF : ContDiffOn ℝ ∞ F D)
    (hState : MapsTo (stateJ J 0) (O ×ˢ Icc 0 T) D)
    (hEquation : ∀ q∈O ×ˢ Icc 0 T, B 0 q=F (stateJ J 0 q)) :
    ∀ k q, q∈O ×ˢ Icc 0 T → B k q=prolong F k (stateJ J k q) := by
  intro k
  induction k with
  | zero => exact hEquation
  | succ k ih =>
      rintro ⟨z,t⟩ ⟨hz,ht⟩
      have hmem := stateJ_mapsTo J hState k (show (z,t)∈O ×ˢ Icc 0 T from ⟨hz,ht⟩)
      have hDiff := ((prolong_contDiffOn hD hF k).differentiableOn (by simp)).differentiableAt
        ((prolongDomain_isOpen hD k).mem_nhds hmem)
      have hc := hDiff.hasFDerivAt.comp z (stateJ_hasFDerivAt J hSpaceJ k hz ht)
      have heq : (fun y => B k (y,t)) =ᶠ[𝓝 z]
          (fun y => prolong F k (stateJ J k (y,t))) := by
        filter_upwards [hO.mem_nhds hz] with y hy
        exact ih (y,t) ⟨hy,ht⟩
      have hb := (hSpaceB k z hz t ht).congr_of_eventuallyEq heq.symm
      exact hb.unique hc

end Yau.LeafProofs.L17BootstrapEvolutionJetsAux
