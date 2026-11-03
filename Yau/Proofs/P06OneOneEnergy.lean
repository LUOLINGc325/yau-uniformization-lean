import Yau.Proofs.P06OneOneHilbert

noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace

namespace Yau.NodeProofs.P06Aux
open Yau Yau.LeafProofs.L03
variable {n : ℕ} {M : ComplexManifold n}

/-- The defining original compact triples approximate every actual energy
vector in its full q+L² norm. -/
theorem hodgeEnergyCore_approximation (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (u : HodgeEnergySpace g μ hμ) :
    ∃ (As : ℕ → RealForm M 2) (hs : ∀ j, SmoothRealForm (As j))
      (hc : ∀ j, CompactlySupportedRealForm (As j)),
      Tendsto (fun j => hodgeEnergyCore g μ hμ (As j) (hs j) (hc j)) atTop (𝓝 u) := by
  have hu : (u : HodgeEnergyAmbient g μ) ∈ closure (hodgeEnergyCoreSet g μ hμ) := by
    rw [← hodgeEnergySubmodule_eq_closure]
    exact u.property
  obtain ⟨p, hp, ht⟩ := mem_closure_iff_seq_limit.mp hu
  change ∀ j, ∃ A : RealForm M 2, ∃ hs : SmoothRealForm A,
    ∃ hc : CompactlySupportedRealForm A, p j = hodgeEnergyCoreTuple g μ hμ A hs hc at hp
  choose As hs hc he using hp
  refine ⟨As, hs, hc, tendsto_subtype_rng.mpr ?_⟩
  change Tendsto (fun j => hodgeEnergyCoreTuple g μ hμ (As j) (hs j) (hc j)) atTop
    (𝓝 (u : HodgeEnergyAmbient g μ))
  have heq : (fun j => hodgeEnergyCoreTuple g μ hμ (As j) (hs j) (hc j)) = p :=
    funext (fun j => (he j).symm)
  rw [heq]
  exact ht

theorem hodgeEnergyCore_projection_le (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (hk : IsKahler g)
    (A : RealForm M 2) (hA : SmoothRealForm A) (hcA : CompactlySupportedRealForm A) :
    hodgeEnergy g μ hμ (hodgeEnergyCore g μ hμ (P06Weitzenbock.oneOneProjection A)
      (P06Weitzenbock.oneOneProjection_smooth A hA)
      (P06Weitzenbock.oneOneProjection_compact A hcA)) ≤
      hodgeEnergy g μ hμ (hodgeEnergyCore g μ hμ A hA hcA) := by
  rw [hodgeEnergyCore_energy, hodgeEnergyCore_energy]
  exact P06Weitzenbock.projection_q_le g μ hμ hk A hA hcA

/-- The actual orthogonal type projection preserves the original closed
energy domain and decreases q, by compact-core approximation and the sharp
weak-limit theorem. -/
theorem hodgeEnergy_oneOneProjection (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (hk : IsKahler g)
    (u : HodgeEnergySpace g μ hμ) :
    ∃ v : HodgeEnergySpace g μ hμ,
      hodgeEnergyValue g μ hμ v = oneOneProjectionHilbert g μ (hodgeEnergyValue g μ hμ u) ∧
        hodgeEnergy g μ hμ v ≤ hodgeEnergy g μ hμ u := by
  obtain ⟨As, hs, hc, ht⟩ := hodgeEnergyCore_approximation g μ hμ u
  let w (j : ℕ) : HodgeEnergySpace g μ hμ :=
    hodgeEnergyCore g μ hμ (P06Weitzenbock.oneOneProjection (As j))
      (P06Weitzenbock.oneOneProjection_smooth (As j) (hs j))
      (P06Weitzenbock.oneOneProjection_compact (As j) (hc j))
  have hval := (oneOneProjectionHilbert g μ).continuous.continuousAt.tendsto.comp
    ((hodgeEnergyValue g μ hμ).continuous.continuousAt.tendsto.comp ht)
  have heq (j : ℕ) : hodgeEnergyValue g μ hμ (w j) = oneOneProjectionHilbert g μ
      (hodgeEnergyValue g μ hμ (hodgeEnergyCore g μ hμ (As j) (hs j) (hc j))) := by
    change realizeActualForm g μ (P06Weitzenbock.oneOneProjection (As j)) _ =
      oneOneProjectionHilbert g μ (realizeActualForm g μ (As j) _)
    rw [oneOneProjectionHilbert_realize]
  have hw : Tendsto (fun j => hodgeEnergyValue g μ hμ (w j)) atTop
      (𝓝 (oneOneProjectionHilbert g μ (hodgeEnergyValue g μ hμ u))) := by
    simpa only [heq, Function.comp_def] using hval
  have hq : ∀ j, hodgeEnergy g μ hμ (w j) ≤
      hodgeEnergy g μ hμ (hodgeEnergyCore g μ hμ (As j) (hs j) (hc j)) :=
    fun j => hodgeEnergyCore_projection_le g μ hμ hk (As j) (hs j) (hc j)
  have henergy : Tendsto (fun j => hodgeEnergy g μ hμ
      (hodgeEnergyCore g μ hμ (As j) (hs j) (hc j))) atTop (𝓝 (hodgeEnergy g μ hμ u)) := by
    exact (((hodgeEnergyExterior g μ hμ).continuous.continuousAt.tendsto.comp ht).norm.pow 2).add
      (((hodgeEnergyLower g μ hμ).continuous.continuousAt.tendsto.comp ht).norm.pow 2)
  exact hodgeEnergy_strong_image_limit g μ hμ w _ _ _ hw hq henergy

end Yau.NodeProofs.P06Aux
