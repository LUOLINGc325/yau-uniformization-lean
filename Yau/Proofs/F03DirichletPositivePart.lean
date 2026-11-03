import Yau.Proofs.F03DirichletNormalContraction
import Yau.LeafProofs.L19HeatMarkovPositivity

/-! Positive parts lie in the genuine supported energy closure. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace
namespace Yau.Proofs.F03Aux
open Yau LeafProofs.L19Aux
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {n : ℕ} {M : ComplexManifold n}

local instance (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) :
    CompleteSpace (DirichletEnergy g μ hμ O) := dirichletEnergy_completeSpace g μ hμ O

theorem normalClipL2_posPart {α : Type*} [MeasurableSpace α]
    (ν : Measure α) (K : ℝ) (hK : 0 ≤ K) (f : Lp ℝ 2 ν) :
    normalClipL2 ν K hK (Lp.posPart f) = normalClipL2 ν K hK f := by
  apply Lp.ext
  filter_upwards [normalClipL2_coe ν K hK (Lp.posPart f),
    normalClipL2_coe ν K hK f,Lp.coeFn_posPart f] with x hp hf hpos
  rw [hp,hf,hpos]
  rcases le_total (f x) 0 with hx | hx
  · rw [max_eq_right hx,normalClip_zero hK]
    exact (max_eq_left ((min_le_right K (f x)).trans hx)).symm
  · rw [max_eq_left hx]

/-- The actual bounded clips converge to the actual L² positive part. -/
theorem normalClipL2_tendsto_posPart {α : Type*} [MeasurableSpace α]
    (ν : Measure α) (f : Lp ℝ 2 ν) :
    Tendsto (fun k : ℕ => normalClipL2 ν ((k : ℝ)+1) (by positivity) f)
      atTop (𝓝 (Lp.posPart f)) := by
  have hp : ∀ᵐ x ∂ν, 0 ≤ Lp.posPart f x := by
    filter_upwards [Lp.coeFn_posPart f] with x hx
    rw [hx]
    exact le_max_right _ _
  simpa only [normalClipL2_posPart] using normalClipL2_tendsto_of_nonneg ν (Lp.posPart f) hp

/-- Positive parts preserve the actual supported energy space and cannot
increase its physical closed energy. This is proved from supported smooth
clips and Hilbert weak compactness, without a trace characterization. -/
theorem dirichletEnergy_posPart_L2 (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) (hO : MeasurableSet O)
    (u : DirichletEnergy g μ hμ O) :
    ∃ v : DirichletEnergy g μ hμ O,
      dirichletL2 g μ hμ O v = Lp.posPart (dirichletL2 g μ hμ O u) ∧
      ‖v‖ ^ 2 - ‖dirichletL2 g μ hμ O v‖ ^ 2 ≤
        ‖u‖ ^ 2 - ‖dirichletL2 g μ hμ O u‖ ^ 2 := by
  classical
  let H := DirichletEnergy g μ hμ O
  let J := dirichletL2 g μ hμ O
  let K : ℕ → ℝ := fun k => (k : ℝ)+1
  have hK (k : ℕ) : 0 ≤ K k := by dsimp [K]; positivity
  have hc (k : ℕ) := dirichletEnergy_normalClip_L2 g μ hμ O hO u (K k) (hK k)
  choose w hwJ hwE using hc
  let z := Lp.posPart (J u)
  have hstrong : Tendsto (fun k => J (w k)) atTop (𝓝 z) := by
    simpa only [hwJ,K,J,z] using normalClipL2_tendsto_posPart (μ.restrict O) (J u)
  have hnorm (k : ℕ) : ‖J (w k)‖ ≤ ‖J u‖ := by
    rw [hwJ]
    simpa only [normalClipL2,NNReal.coe_one,one_mul] using
      (normalClip_lipschitz (K k)).norm_compLp_le (normalClip_zero (hK k)) (J u)
  have hbound : ∀ᶠ k in atTop, ‖w k‖ ≤ ‖u‖ := by
    apply Eventually.of_forall
    intro k
    have he := hwE k
    have hn := hnorm k
    nlinarith [norm_nonneg (w k),norm_nonneg u,norm_nonneg (J (w k)),norm_nonneg (J u)]
  let a : ℕ → ℝ := fun k => ‖u‖ ^ 2 - ‖J u‖ ^ 2 + ‖J (w k)‖ ^ 2
  have hupper : ∀ᶠ k in atTop, ‖w k‖ ^ 2 ≤ a k := by
    exact Eventually.of_forall (fun k => by dsimp only [a]; linarith only [hwE k])
  have ha : Tendsto a atTop (𝓝 (‖u‖ ^ 2 - ‖J u‖ ^ 2 + ‖z‖ ^ 2)) :=
    tendsto_const_nhds.add (hstrong.norm.pow 2)
  obtain ⟨v,hvJ,hv⟩ := hilbert_strong_image_limit J w z a _ ‖u‖ hbound hstrong hupper ha
  refine ⟨v,hvJ,?_⟩
  change ‖v‖ ^ 2 - ‖J v‖ ^ 2 ≤ ‖u‖ ^ 2 - ‖J u‖ ^ 2
  rw [hvJ]
  linarith

end Yau.Proofs.F03Aux
