import Yau.Proofs.C07JointLift

/-! Compactness in the homotopy parameter gives one late time for all original rows. -/

open scoped Manifold Topology

noncomputable section

namespace Yau.Proofs.C07Aux

open Yau Yau.Blueprint Set

variable {n : ℕ} {M : ComplexManifold n}

theorem eventually_joint_lift_of_local_parameter
    (Φ : ℝ → ComplexVector n → M.Carrier)
    (H : C(unitInterval × unitInterval, M.Carrier)) {r T₀ : ℝ}
    (hΦ : ∀ t, T₀ ≤ t → IsLocalBiholomorphism (Φ t) r)
    (hlocal : ∀ s : unitInterval, ∃ N : Set unitInterval, IsOpen N ∧ s ∈ N ∧
      ∃ S : ℝ, ∀ t, S ≤ t → ∃ E : unitInterval × N → ComplexVector n,
        Continuous E ∧ (∀ z, E (0, z) = 0) ∧
        ∀ p, E p ∈ Metric.ball 0 r ∧ Φ t (E p) = H (p.1, p.2.1)) :
    ∃ S : ℝ, T₀ ≤ S ∧ ∀ t, S ≤ t → ∃ E : unitInterval × unitInterval → ComplexVector n,
      Continuous E ∧ (∀ s, E (0, s) = 0) ∧
      ∀ p, E p ∈ Metric.ball 0 r ∧ Φ t (E p) = H p := by
  classical
  choose N hNo hNs S hS using hlocal
  obtain ⟨J, hJ⟩ := (isCompact_univ : IsCompact (univ : Set unitInterval)).elim_finite_subcover
    N hNo (fun s _ => mem_iUnion.mpr ⟨s, hNs s⟩)
  let T := max T₀ (∑ j ∈ J, max 0 (S j))
  have hT₀ : T₀ ≤ T := le_max_left _ _
  have hTj (j : unitInterval) (hj : j ∈ J) : S j ≤ T :=
    (le_max_right 0 (S j)).trans
      ((Finset.single_le_sum (fun i _ => le_max_left 0 (S i)) hj).trans (le_max_right _ _))
  refine ⟨T, hT₀, ?_⟩
  intro t ht
  have hex (j : J) : ∃ E : unitInterval × N j.1 → ComplexVector n,
      Continuous E ∧ (∀ z, E (0, z) = 0) ∧
      ∀ p, E p ∈ Metric.ball 0 r ∧ Φ t (E p) = H (p.1, p.2.1) :=
    hS j.1 t ((hTj j.1 j.2).trans ht)
  choose e he he₀ hep using hex
  choose i hi hNi using (fun s : unitInterval => mem_iUnion₂.mp (hJ (mem_univ s)))
  let j : unitInterval → J := fun s => ⟨i s, hi s⟩
  let z : ∀ s : unitInterval, N (j s).1 := fun s => ⟨s, hNi s⟩
  let E : unitInterval × unitInterval → ComplexVector n :=
    fun p => e (j p.2) (p.1, z p.2)
  have hE₀ (s : unitInterval) : E (0, s) = 0 := he₀ (j s) (z s)
  have hEp (p : unitInterval × unitInterval) :
      E p ∈ Metric.ball 0 r ∧ Φ t (E p) = H p := hep (j p.2) (p.1, z p.2)
  have hstart : Continuous (fun s => E (0, s)) :=
    continuous_const.congr fun s => (hE₀ s).symm
  have hrows (s : unitInterval) : Continuous (fun u => E (u, s)) := by
    have hmap : Continuous (fun u : unitInterval => (u, z s)) :=
      continuous_id.prodMk continuous_const
    exact (he (j s)).comp hmap
  exact ⟨E, chart_lift_joint_continuous (hΦ t (hT₀.trans ht)) H E
    (fun p => (hEp p).1) (fun p => (hEp p).2) hstart hrows, hE₀, hEp⟩

end Yau.Proofs.C07Aux
