import Yau.Proofs.P06OneOneEnergy

noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace

namespace Yau.NodeProofs.P06Aux
open Yau Yau.LeafProofs.L03
variable {n : ℕ} {M : ComplexManifold n}

def oneOneEnergyValue (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (hk : IsKahler g)
    (u : HodgeEnergySpace g μ hμ) : HodgeEnergySpace g μ hμ :=
  (hodgeEnergy_oneOneProjection g μ hμ hk u).choose

theorem oneOneEnergyValue_value (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (hk : IsKahler g) (u : HodgeEnergySpace g μ hμ) :
    hodgeEnergyValue g μ hμ (oneOneEnergyValue g μ hμ hk u) =
      oneOneProjectionHilbert g μ (hodgeEnergyValue g μ hμ u) :=
  (hodgeEnergy_oneOneProjection g μ hμ hk u).choose_spec.1

theorem oneOneEnergyValue_q_le (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (hk : IsKahler g) (u : HodgeEnergySpace g μ hμ) :
    hodgeEnergy g μ hμ (oneOneEnergyValue g μ hμ hk u) ≤ hodgeEnergy g μ hμ u :=
  (hodgeEnergy_oneOneProjection g μ hμ hk u).choose_spec.2

def oneOneProjectionEnergyLinear (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (hk : IsKahler g) :
    HodgeEnergySpace g μ hμ →ₗ[ℝ] HodgeEnergySpace g μ hμ where
  toFun := oneOneEnergyValue g μ hμ hk
  map_add' u v := by
    apply hodgeEnergyValue_injective g μ hμ
    simp only [oneOneEnergyValue_value, map_add]
  map_smul' r u := by
    apply hodgeEnergyValue_injective g μ hμ
    change hodgeEnergyValue g μ hμ (oneOneEnergyValue g μ hμ hk (r • u)) =
      hodgeEnergyValue g μ hμ (r • oneOneEnergyValue g μ hμ hk u)
    simp only [oneOneEnergyValue_value, map_smul]

theorem oneOneProjectionEnergyLinear_norm_le (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (hk : IsKahler g) (u : HodgeEnergySpace g μ hμ) :
    ‖oneOneProjectionEnergyLinear g μ hμ hk u‖ ≤ ‖u‖ := by
  have hv := oneOneEnergyValue_value g μ hμ hk u
  have hq := oneOneEnergyValue_q_le g μ hμ hk u
  have hn := pow_le_pow_left₀ (norm_nonneg _)
    (oneOneProjectionHilbert_norm_le g μ (hodgeEnergyValue g μ hμ u)) 2
  have hs : ‖oneOneProjectionEnergyLinear g μ hμ hk u‖ ^ 2 ≤ ‖u‖ ^ 2 := by
    change ‖oneOneEnergyValue g μ hμ hk u‖ ^ 2 ≤ ‖u‖ ^ 2
    rw [hodgeEnergy_norm_sq, hodgeEnergy_norm_sq, hv]
    exact add_le_add hn hq
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hs

def oneOneProjectionEnergy (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (hk : IsKahler g) :
    HodgeEnergySpace g μ hμ →L[ℝ] HodgeEnergySpace g μ hμ :=
  (oneOneProjectionEnergyLinear g μ hμ hk).mkContinuous 1
    (fun u => by simpa only [one_mul] using oneOneProjectionEnergyLinear_norm_le g μ hμ hk u)

theorem oneOneProjectionEnergy_value (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (hk : IsKahler g) (u : HodgeEnergySpace g μ hμ) :
    hodgeEnergyValue g μ hμ (oneOneProjectionEnergy g μ hμ hk u) =
      oneOneProjectionHilbert g μ (hodgeEnergyValue g μ hμ u) :=
  oneOneEnergyValue_value g μ hμ hk u

theorem oneOneProjectionEnergy_q_le (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (hk : IsKahler g) (u : HodgeEnergySpace g μ hμ) :
    hodgeEnergy g μ hμ (oneOneProjectionEnergy g μ hμ hk u) ≤ hodgeEnergy g μ hμ u :=
  oneOneEnergyValue_q_le g μ hμ hk u

theorem oneOneProjectionEnergy_core (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (hk : IsKahler g)
    (A : RealForm M 2) (hA : SmoothRealForm A) (hcA : CompactlySupportedRealForm A) :
    oneOneProjectionEnergy g μ hμ hk (hodgeEnergyCore g μ hμ A hA hcA) =
      hodgeEnergyCore g μ hμ (P06Weitzenbock.oneOneProjection A)
        (P06Weitzenbock.oneOneProjection_smooth A hA)
        (P06Weitzenbock.oneOneProjection_compact A hcA) := by
  apply hodgeEnergyValue_injective g μ hμ
  rw [oneOneProjectionEnergy_value]
  exact oneOneProjectionHilbert_realize g μ A _

theorem oneOneProjectionEnergy_fixed (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (hk : IsKahler g)
    (u : HodgeEnergySpace g μ hμ)
    (hu : oneOneProjectionHilbert g μ (hodgeEnergyValue g μ hμ u) = hodgeEnergyValue g μ hμ u) :
    oneOneProjectionEnergy g μ hμ hk u = u := by
  apply hodgeEnergyValue_injective g μ hμ
  rw [oneOneProjectionEnergy_value, hu]

/-- Compact smooth real (1,1) forms approximate every (1,1) vector of the
original closed energy domain in the full q+L² topology. -/
theorem hodgeEnergyCore_oneOne_approximation (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (hk : IsKahler g)
    (u : HodgeEnergySpace g μ hμ)
    (hu : oneOneProjectionHilbert g μ (hodgeEnergyValue g μ hμ u) = hodgeEnergyValue g μ hμ u) :
    ∃ (As : ℕ → RealForm M 2) (hs : ∀ j, SmoothRealForm (As j))
      (hc : ∀ j, CompactlySupportedRealForm (As j)),
      (∀ j, RealOneOne (As j)) ∧
      Tendsto (fun j => hodgeEnergyCore g μ hμ (As j) (hs j) (hc j)) atTop (𝓝 u) := by
  obtain ⟨As, hs, hc, ht⟩ := hodgeEnergyCore_approximation g μ hμ u
  refine ⟨fun j => P06Weitzenbock.oneOneProjection (As j),
    fun j => P06Weitzenbock.oneOneProjection_smooth (As j) (hs j),
    fun j => P06Weitzenbock.oneOneProjection_compact (As j) (hc j),
    fun j => P06Weitzenbock.oneOneProjection_type (As j), ?_⟩
  have hp := (oneOneProjectionEnergy g μ hμ hk).continuous.continuousAt.tendsto.comp ht
  simpa only [Function.comp_def, oneOneProjectionEnergy_core, oneOneProjectionEnergy_fixed g μ hμ hk u hu] using hp

end Yau.NodeProofs.P06Aux
