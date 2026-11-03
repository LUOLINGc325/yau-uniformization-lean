import Yau.Proofs.F04ZeroLevel
import Yau.Proofs.F04SupportedCutoff
import Yau.Proofs.F04ScalarExteriorLocality
import Yau.Proofs.F04SmoothCompositionCore

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold InnerProductSpace

noncomputable section

namespace Yau.F04Proof

open Yau.Proofs.F03Aux Yau.LeafProofs.L03

variable {n : ℕ} {M : ComplexManifold n}

/-- Locality on a smooth level is proved by a countable family of actual
supported smooth cutoffs. The smooth shift itself need not belong to H10. -/
theorem dirichlet_differential_eq_smooth_on_level
    (g : SmoothMetric M) (hK : IsKahler g) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) (hO : IsOpen O)
    (r : M.Carrier → ℝ) (hr : SmoothFn r)
    (u : DirichletEnergy g μ hμ O) (A : RealForm M 1)
    (hA : L2RealForm g.form (μ.restrict O) A)
    (hDu : dirichletD g μ hμ O u = realizeL2Form g (μ.restrict O) (L2FormSpace.ofSection A hA)) :
    ∀ᵐ x ∂μ.restrict O, dirichletL2 g μ hμ O u x = r x → A x = scalarExterior r x := by
  classical
  have hcut (i : O) := exists_supported_smooth_cutoff ({i.val} : Set M.Carrier) O
    isCompact_singleton hO (singleton_subset_iff.mpr i.property)
  choose η W hη hcη hηO hWo hKW hWO hηone hηrange using hcut
  have hcover : O ⊆ ⋃ i : O, W i := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, hKW ⟨x, hx⟩ (mem_singleton x)⟩
  obtain ⟨s, hs, hscov⟩ := (HereditarilyLindelofSpace.isLindelof O).elim_countable_subcover W hWo hcover
  let v (i : O) : dirichletCore g μ hμ O :=
    ⟨⟨fun x => η i x * r x, (fun c => (hη i c).mul (hr c)), (hcη i).mul_right⟩,
      tsupport_mul_subset_left.trans (hηO i)⟩
  have hv (i : O) : EqOn ((v i).val : M.Carrier → ℝ) r (W i) := by
    intro x hx
    change η i x * r x = r x
    rw [hηone i x hx, one_mul]
  have hvD (i : O) (x : M.Carrier) (hx : x ∈ W i) :
      scalarExterior (v i).val x = scalarExterior r x :=
    scalarExterior_congr_on_open (v i).val.2.1 hr (W i) (hWo i) (hv i) x hx
  have hlocal (i : O) : ∀ᵐ x ∂μ.restrict O,
      x ∈ W i → dirichletL2 g μ hμ O u x = r x → A x = scalarExterior r x := by
    let w := u - dirichletCoreToEnergy g μ hμ O (v i)
    have hdv := scalarExterior_l2_restrict g μ hμ O (v i).val.2.1 (v i).val.2.2
    have hAd : L2RealForm g.form (μ.restrict O) (A - scalarExterior (v i).val) :=
      (l2FormSubmodule g (μ.restrict O) 1).sub_mem hA hdv
    have hDw : dirichletD g μ hμ O w =
        realizeL2Form g (μ.restrict O) (L2FormSpace.ofSection (A - scalarExterior (v i).val) hAd) := by
      dsimp only [w]
      rw [map_sub, hDu, dirichletD_core, scalarEnergyDomainD, realize_section_sub]
    have hz := dirichlet_differential_zero_on_zero_level g hK μ hμ O hO.measurableSet
      w (A - scalarExterior (v i).val) hAd hDw
    have hJw : ∀ᵐ x ∂μ.restrict O,
        dirichletL2 g μ hμ O w x = dirichletL2 g μ hμ O u x - (v i).val x := by
      filter_upwards [Lp.coeFn_sub (dirichletL2 g μ hμ O u)
          (dirichletL2 g μ hμ O (dirichletCoreToEnergy g μ hμ O (v i))),
        dirichletCoreL2_ae g μ hμ O (v i)] with x hs hvx
      dsimp only [w]
      rw [map_sub, hs]
      simp only [Pi.sub_apply, hvx]
    filter_upwards [hz, hJw] with x hz hxw
    intro hx hlevel
    have hx0 : dirichletL2 g μ hμ O w x = 0 := by
      rw [hxw, hv i hx, hlevel, sub_self]
    have hzero := hz hx0
    change A x - scalarExterior (v i).val x = 0 at hzero
    rw [hvD i x hx] at hzero
    exact sub_eq_zero.mp hzero
  have hAll : (⋂ i ∈ s, {x | x ∈ W i → dirichletL2 g μ hμ O u x = r x → A x = scalarExterior r x})
      ∈ ae (μ.restrict O) :=
    (countable_bInter_mem hs).mpr (fun i _ => hlocal i)
  filter_upwards [hAll, ae_restrict_mem hO.measurableSet] with x hx hxo
  intro hlevel
  obtain ⟨i, his, hxi⟩ := mem_iUnion₂.mp (hscov hxo)
  have hall : ∀ i ∈ s, x ∈ W i → dirichletL2 g μ hμ O u x = r x → A x = scalarExterior r x := by
    simpa only [mem_iInter, mem_ofPred_eq] using hx
  exact hall i his hxi hlevel

end Yau.F04Proof
