import Yau.Proofs.F04LocalFormMarkov
import Yau.Proofs.F04PositiveWeakMaximum
import Yau.Proofs.F04LpOrderPairing
import Yau.Proofs.F04VariationalTime
import Yau.Proofs.F04WeakTimeSubtract

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold InnerProductSpace

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Yau.F04Proof

open Yau.Proofs.F03Aux Yau.MassTargetStatements

variable {n : ℕ} {M : ComplexManifold n}

local instance (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) :
    CompleteSpace (DirichletEnergy g μ hμ O) := dirichletEnergy_completeSpace g μ hμ O

/-- Source order gives order of the original continuous weak-solution traces
 for the actual nonsymmetric fixed-volume form and its one coercive shift. -/
theorem variationalSolution_order
    (g : SmoothMetric M) (hK : IsKahler g) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) (hO : IsOpen O)
    (h : ℝ → HermitianField M) {T C α shift : ℝ} (hT : 0 < T)
    (B : ℝ → DirichletEnergy g μ hμ O →L[ℝ] EnergyDual (DirichletEnergy g μ hμ O))
    (hForm : IntrinsicFormBinding g.form μ O h T C α shift
      (dirichletL2 g μ hμ O) (energyRepresentative g μ hμ O) B)
    (f q : ℝ → FixedPivot μ O) (U V : ℝ → DirichletEnergy g μ hμ O)
    (R S : ℝ → EnergyDual (DirichletEnergy g μ hμ O)) (a b : ℝ → FixedPivot μ O)
    (hSol : VariationalSolution μ O T (dirichletL2 g μ hμ O) B f U R a)
    (hSol₂ : VariationalSolution μ O T (dirichletL2 g μ hμ O) B q V S b)
    (hSrc : ∀ᵐ t ∂volume.restrict (Ioo 0 T), ∀ᵐ x ∂μ.restrict O, f t x ≤ q t x) :
    ∀ t ∈ Icc 0 T, ∀ᵐ x ∂μ.restrict O, a t x ≤ b t x := by
  let j := dirichletL2 g μ hμ O
  have hw := variationalSolution_weak_time μ O hT j B f U R a hSol
  have hw₂ := variationalSolution_weak_time μ O hT j B q V S b hSol₂
  rcases hSol with ⟨hU, hR, ha, ha0, hae, _hscalar, hEq⟩
  rcases hSol₂ with ⟨hV, hS, hb, hb0, hbae, _hscalar₂, hEq₂⟩
  let UD := fun t => U t - V t
  let RD := fun t => R t - S t
  let ad := fun t => a t - b t
  have hUD : MemLp UD 2 (volume.restrict (Ioo 0 T)) := hU.sub hV
  have hRD := hR.sub hS
  have hwd := hilbert_weak_time_subtract j hT hU hV hR hS hw hw₂
  have hda : ∀ᵐ t ∂volume.restrict (Ioo 0 T), j (UD t) = ad t := by
    filter_upwards [hae, hbae] with t hat hbt
    dsimp only [UD, ad]
    rw [map_sub, ← hat, ← hbt]
  have hInit : ∀ᵐ x ∂μ.restrict O, ad 0 x ≤ 0 := by
    dsimp only [ad]
    rw [ha0, hb0, sub_self]
    filter_upwards [Lp.coeFn_zero (E := ℝ) (p := 2) (μ := μ.restrict O)] with x hx
    rw [hx]
    simp only [Pi.zero_apply, le_refl]
  have hBound : ∀ᵐ t ∂volume.restrict (Ioo 0 T),
      RD t (dirichletPosPart g μ hμ O hO.measurableSet (UD t)) ≤ shift * ‖Lp.posPart (ad t)‖ ^ 2 := by
    filter_upwards [hEq, hEq₂, hda, hSrc, ae_restrict_mem measurableSet_Ioo] with t het he₂t hdt hSrcT ht
    let w := dirichletPosPart g μ hμ O hO.measurableSet (UD t)
    have hJw : j w = Lp.posPart (ad t) := by
      change dirichletL2 g μ hμ O (dirichletPosPart g μ hμ O hO.measurableSet (UD t)) = _
      rw [(dirichletPosPart_spec g μ hμ O hO.measurableSet (UD t)).1, hdt]
    have hW0 : ∀ᵐ x ∂μ.restrict O, 0 ≤ j w x := by
      rw [hJw]
      filter_upwards [Lp.coeFn_posPart (ad t)] with x hx
      rw [hx]
      exact le_max_right _ _
    have hInner := lp_inner_sub_nonpos_of_ae (μ.restrict O) (f t) (q t) (j w) hSrcT hW0
    have he : RD t w + B t (UD t) w = inner ℝ (f t - q t) (j w) := by
      have h1 := het w
      have h2 := he₂t w
      change (R t w - S t w) + B t (U t - V t) w = inner ℝ (f t - q t) (j w)
      rw [(B t).map_sub (U t) (V t), inner_sub_left]
      change (R t w - S t w) + (B t (U t) w - B t (V t) w) = _
      linarith only [h1, h2]
    have hMarkov := intrinsicForm_posPart_test g hK μ hμ O hO h T C α shift B hForm t (Ioo_subset_Icc_self ht) (UD t)
    change B t (UD t) w = B t w w at hMarkov
    rw [hMarkov] at he
    have hc := (hForm.2.2.2.2 t (Ioo_subset_Icc_self ht)).2.1 w
    rw [hJw] at hc
    have hα0 : 0 ≤ α * ‖w‖ ^ 2 := mul_nonneg hForm.2.1.le (sq_nonneg _)
    change RD t w ≤ shift * ‖Lp.posPart (ad t)‖ ^ 2
    linarith only [he, hc, hα0, hInner]
  have hMax := dirichlet_posPart_weak_maximum g hK μ hμ O hO.measurableSet hT hUD hRD hwd
    ad (ha.sub hb) hda shift hForm.2.2.1 hInit hBound
  intro t ht
  filter_upwards [hMax t ht, Lp.coeFn_sub (a t) (b t)] with x hx hs
  rw [hs, Pi.sub_apply] at hx
  exact sub_nonpos.mp hx

end Yau.F04Proof
