import Yau.Proofs.P08HeatBarrierDecay
import Yau.Proofs.P08HeatMeasureMoments

/-! Heat submean for actual smooth linear-growth subharmonic data. Its heat
measure, mass and integrability are all the internally proved actual ones. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff Manifold Matrix ComplexOrder
namespace Yau.NodeProofs.P08Aux
open Yau Yau.LeafProofs L12Aux L18Aux L19Aux HeatMeasure
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000

theorem nonnegative_subharmonic_linear_heat_submean (hn : 0 < n) (g : SmoothMetric M)
    (hcomplete : IsComplete g) (hK : IsKahler g) (hRic : ∀ x, (ricci g.form x).PosSemidef)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ) (o : M.Carrier)
    {v : M.Carrier → ℝ} (hv : SmoothFn v) (hv0 : ∀ x, 0 ≤ v x)
    (hvΔ : ∀ x, 0 ≤ laplacian g.form v x) {B A t : ℝ} (hB : 0 ≤ B) (hA : 0 ≤ A)
    (hbound : ∀ x, v x ≤ B + A * distFrom g.form o x) (ht : 0 < t) :
    v o ≤ ∫ x, v x ∂heatEvalMeasure hn g hcomplete hK hRic μ hμ o t ht := by
  let ν := heatEvalMeasure hn g hcomplete hK hRic μ hμ o t ht
  have hvi : Integrable v ν := heatEvalMeasure_integrable_linear hn g hcomplete hK hRic μ hμ o t ht
    (continuous_of_smoothFn hv).aestronglyMeasurable (fun x => by rw [abs_of_nonneg (hv0 x)]; exact hbound x)
  have habs : ν ≪ μ := heatEvalMeasure_absolutelyContinuous hn g hcomplete hK hRic μ hμ o t ht
  apply le_of_forall_pos_le_add
  intro ε hε
  let D : ℝ := (B + A + 1) / (1 - Real.exp (-1)) * (4 * n) * t
  let R : ℝ := max 1 (D / ε + 1)
  have hRone : 1 ≤ R := le_max_left _ _
  have hR : 0 < R := lt_of_lt_of_le zero_lt_one hRone
  obtain ⟨k, hk, hbar⟩ := compact_heat_submean_barrier hn g hK hRic μ hμ o hv hv0 hvΔ hB hA hbound hR
  have hheat : scalarClassicalHeat hn g hK μ hμ (scalarEnergyDomainL2 g μ hμ k) o t ≤ ∫ x, v x ∂ν := by
    rw [← heatEvalMeasure_integral hn g hcomplete hK hRic μ hμ o t ht]
    apply integral_mono_ae (heatEvalMeasure_integrable hn g hcomplete hK hRic μ hμ o t ht _) hvi
    filter_upwards [habs.ae_eq (scalarEnergyDomainL2_coe g μ hμ k)] with x hx
    rw [hx]
    exact (hk x).2
  have herr := heat_submean_barrier_error_le n hB hA hRone ht
  have hsmall : D / R ≤ ε := by
    apply (div_le_iff₀ hR).mpr
    have hDR : D / ε ≤ R := by
      dsimp only [R]
      linarith [le_max_right (1 : ℝ) (D / ε + 1)]
    have hh := (div_le_iff₀ hε).mp hDR
    nlinarith
  have hh := hbar t ht
  change v o ≤ (∫ x, v x ∂ν) + ε
  dsimp only [D] at hsmall
  linarith

/-- A fixed finite lower bound suffices; its size cancels because the actual
heat evaluation measure has mass one. -/
theorem smooth_subharmonic_linear_heat_submean (hn : 0 < n) (g : SmoothMetric M)
    (hcomplete : IsComplete g) (hK : IsKahler g) (hRic : ∀ x, (ricci g.form x).PosSemidef)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ) (o : M.Carrier)
    {w : M.Carrier → ℝ} (hw : SmoothFn w) (hΔ : ∀ x, 0 ≤ laplacian g.form w x)
    {b A t : ℝ} (hb : ∀ x, b ≤ w x) (hA : 0 ≤ A)
    (hgrowth : ∀ x, w x ≤ A * (1 + distFrom g.form o x)) (ht : 0 < t) :
    w o ≤ ∫ x, w x ∂heatEvalMeasure hn g hcomplete hK hRic μ hμ o t ht := by
  let ν := heatEvalMeasure hn g hcomplete hK hRic μ hμ o t ht
  letI : IsFiniteMeasure ν := heatEvalMeasure_isFinite hn g hcomplete hK hRic μ hμ o t ht
  let v : M.Carrier → ℝ := fun x => w x - b
  have hv : SmoothFn v := smoothFn_sub hw (smoothFn_const b)
  have hv0 (x : M.Carrier) : 0 ≤ v x := sub_nonneg.mpr (hb x)
  have hvΔ (x : M.Carrier) : 0 ≤ laplacian g.form v x := by
    change 0 ≤ laplacian g.form (fun y => w y + -b) x
    rw [laplacian_add_const g.form hw (-b) x]
    exact hΔ x
  have hvgrowth (x : M.Carrier) : v x ≤ (A + |b|) + A * distFrom g.form o x := by
    have hh := hgrowth x
    dsimp only [v]
    linarith [neg_abs_le b]
  have hwabs (x : M.Carrier) : |w x| ≤ (A + |b|) + A * distFrom g.form o x := by
    have hr : 0 ≤ distFrom g.form o x := g.induced_distance_nonneg o x
    have hAr := mul_nonneg hA hr
    exact abs_le.mpr ⟨by nlinarith [hb x, neg_abs_le b], by nlinarith [hgrowth x, abs_nonneg b]⟩
  have hwi : Integrable w ν := heatEvalMeasure_integrable_linear hn g hcomplete hK hRic μ hμ o t ht
    (continuous_of_smoothFn hw).aestronglyMeasurable hwabs
  have hsub := nonnegative_subharmonic_linear_heat_submean hn g hcomplete hK hRic μ hμ o hv hv0 hvΔ
    (add_nonneg hA (abs_nonneg b)) hA hvgrowth ht
  have hmass : ν Set.univ = 1 := heatEvalMeasure_mass hn g hcomplete hK hRic μ hμ o t ht
  have hconst : (∫ _x, b ∂ν) = b := by simp only [integral_const, Measure.real, hmass, ENNReal.toReal_one, one_smul]
  change w o - b ≤ ∫ x, w x - b ∂ν at hsub
  rw [integral_sub hwi (integrable_const b), hconst] at hsub
  linarith

end Yau.NodeProofs.P08Aux
