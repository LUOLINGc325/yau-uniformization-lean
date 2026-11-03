import Yau.LeafProofs.L17BootstrapEvolutionJetsProlong

open Set Filter
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17BootstrapEvolutionJetsAux
open L17BootstrapClosedSlabAux
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {O : Set E} (hO : IsOpen O) (hconv : Convex ℝ O) {T : ℝ} (hT : 0<T)
  {J B : (k : ℕ) → E × ℝ → Jet E ℝ k}
  (hContJ : ∀ k, ContinuousOn (J k) (O ×ˢ Icc 0 T))
  (hContB : ∀ k, ContinuousOn (B k) (O ×ˢ Icc 0 T))
  (hSpaceJ : ∀ k z, z∈O → ∀ t, t∈Icc 0 T →
    HasFDerivAt (fun y => J k (y,t)) (J (k+1) (z,t)) z)
  (hSpaceB : ∀ k z, z∈O → ∀ t, t∈Icc 0 T →
    HasFDerivAt (fun y => B k (y,t)) (B (k+1) (z,t)) z)
  (hTime : ∀ k z, z∈O → ∀ t, t∈Icc 0 T →
    HasDerivWithinAt (fun s => J k (z,s)) (B k (z,t)) (Icc 0 T) t)
  {F : State E 0 → ℝ} {D : Set (State E 0)}
  (hD : IsOpen D) (hF : ContDiffOn ℝ ∞ F D)
  (hState : MapsTo (stateJ J 0) (O ×ˢ Icc 0 T) D)
  (hEquation : ∀ q∈O ×ˢ Icc 0 T, B 0 q=F (stateJ J 0 q))

include hO hconv hT hContJ hContB hSpaceJ hSpaceB hTime hD hF hState hEquation

theorem contDiffOn_nat_of_evolution_spatial_jets (m : ℕ) :
    ∀ k, ContDiffOn ℝ m (J k) (O ×ˢ Icc 0 T) := by
  have hB := timeJet_eq_prolong hO hSpaceJ hSpaceB hD hF hState hEquation
  induction m with
  | zero => intro k; exact contDiffOn_zero.mpr (hContJ k)
  | succ m ih =>
      have hBCm : ∀ k, ContDiffOn ℝ m (B k) (O ×ˢ Icc 0 T) := by
        intro k
        have hp := (prolong_contDiffOn hD hF k).of_le
          (show (m : ℕ∞ω) ≤ ∞ by simp)
        exact (hp.comp (stateJ_contDiffOn J ih k) (stateJ_mapsTo J hState k)).congr
          (fun q hq => hB k q hq)
      intro k
      change ContDiffOn ℝ ((m : ℕ∞ω)+1) (J k) (O ×ˢ Icc 0 T)
      let DJ : E × ℝ → (E × ℝ) →L[ℝ] Jet E ℝ k :=
        fun q => productDerivativeCLM E (Jet E ℝ k) (J (k+1) q,B k q)
      have hDJ : ContDiffOn ℝ m DJ (O ×ˢ Icc 0 T) := by
        exact (productDerivativeCLM E (Jet E ℝ k)).contDiff.comp_contDiffOn
          ((ih (k+1)).prodMk (hBCm k))
      have hd : ∀ q∈O ×ˢ Icc 0 T,
          HasFDerivWithinAt (J k) (DJ q) (O ×ˢ Icc 0 T) q := by
        rintro ⟨z,t⟩ hq
        dsimp only [DJ]
        rw [productDerivativeCLM_apply]
        exact hasFDerivWithinAt_of_spatial_time hO hconv hT
          (hContJ k) (hContJ (k+1)) (hContB k) (hSpaceJ k) (hTime k) hq.1 hq.2
      apply (contDiffOn_succ_iff_hasFDerivWithinAt (by simp : (m : ℕ∞ω)≠∞)).mpr
      intro q hq
      refine ⟨O ×ˢ Icc 0 T,?_,?_,DJ,hd,hDJ⟩
      · rw [insert_eq_of_mem hq]
        exact self_mem_nhdsWithin
      · intro h
        simp at h

theorem contDiffOn_infty_of_evolution_spatial_jets :
    (∀ k, ContDiffOn ℝ ∞ (J k) (O ×ˢ Icc 0 T)) ∧
    (∀ k, ContDiffOn ℝ ∞ (B k) (O ×ˢ Icc 0 T)) := by
  have hJ : ∀ k, ContDiffOn ℝ ∞ (J k) (O ×ˢ Icc 0 T) := by
    intro k
    apply contDiffOn_infty.mpr
    intro m
    exact contDiffOn_nat_of_evolution_spatial_jets hO hconv hT hContJ hContB
      hSpaceJ hSpaceB hTime hD hF hState hEquation m k
  refine ⟨hJ,?_⟩
  intro k
  exact ((prolong_contDiffOn hD hF k).comp (stateJ_contDiffOn J hJ k)
    (stateJ_mapsTo J hState k)).congr
      (fun q hq => timeJet_eq_prolong hO hSpaceJ hSpaceB hD hF hState hEquation k q hq)

theorem contDiffOn_infty_of_evolution_eqOn {u : E × ℝ → ℝ}
    (hu : EqOn u (J 0) (O ×ˢ Icc 0 T)) : ContDiffOn ℝ ∞ u (O ×ˢ Icc 0 T) :=
  ((contDiffOn_infty_of_evolution_spatial_jets hO hconv hT hContJ hContB
    hSpaceJ hSpaceB hTime hD hF hState hEquation).1 0).congr hu

end Yau.LeafProofs.L17BootstrapEvolutionJetsAux
