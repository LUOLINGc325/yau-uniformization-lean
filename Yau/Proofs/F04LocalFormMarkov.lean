import Yau.Proofs.F04LocalFormClips
import Yau.Proofs.F04H10Binding

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold InnerProductSpace

noncomputable section

namespace Yau.F04Proof

open Yau.Proofs.F03Aux Yau.MassTargetStatements

variable {n : ℕ} {M : ComplexManifold n}

theorem localCoreForm_posPart_test
    (g : SmoothMetric M) (hK : IsKahler g) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) (hO : MeasurableSet O)
    (H : HermitianField M)
    (B : DirichletEnergy g μ hμ O →L[ℝ] DirichletEnergy g μ hμ O →L[ℝ] ℝ)
    (hCore : ∀ f v : dirichletCore g μ hμ O,
      B (dirichletCoreEmbedding g μ hμ O f) (dirichletCoreEmbedding g μ hμ O v) =
        -(∫ x in O, v.val x * laplacian H f.val x ∂μ))
    (u : DirichletEnergy g μ hμ O) :
    B u (dirichletPosPart g μ hμ O hO u) =
      B (dirichletPosPart g μ hμ O hO u) (dirichletPosPart g μ hμ O hO u) := by
  let p := dirichletPosPart g μ hμ O hO u
  let m := dirichletPosPart g μ hμ O hO (-u)
  have hdec : u = p - m := dirichlet_pos_neg_decomposition g hK μ hμ O hO u
  have hCross : B m p = 0 := localCoreForm_posPart_cross_zero g hK μ hμ O hO H B hCore u
  calc
    B u p = B (p - m) p := congrArg (fun v => B v p) hdec
    _ = B p p - B m p := congrArg
      (fun L : DirichletEnergy g μ hμ O →L[ℝ] ℝ => L p) (B.map_sub p m)
    _ = B p p := by rw [hCross, sub_zero]

theorem localCoreForm_negPart_test
    (g : SmoothMetric M) (hK : IsKahler g) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) (hO : MeasurableSet O)
    (H : HermitianField M)
    (B : DirichletEnergy g μ hμ O →L[ℝ] DirichletEnergy g μ hμ O →L[ℝ] ℝ)
    (hCore : ∀ f v : dirichletCore g μ hμ O,
      B (dirichletCoreEmbedding g μ hμ O f) (dirichletCoreEmbedding g μ hμ O v) =
        -(∫ x in O, v.val x * laplacian H f.val x ∂μ))
    (u : DirichletEnergy g μ hμ O) :
    B u (dirichletPosPart g μ hμ O hO (-u)) =
      -B (dirichletPosPart g μ hμ O hO (-u)) (dirichletPosPart g μ hμ O hO (-u)) := by
  have he := localCoreForm_posPart_test g hK μ hμ O hO H B hCore (-u)
  simp only [map_neg, neg_apply] at he
  linarith only [he]

/-- The registered form's actual test identity gives its exact smooth-core
 formula, in the same initial-volume measure and same supported completion. -/
theorem intrinsicForm_core_formula
    (g : SmoothMetric M) (hK : IsKahler g) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) (hO : IsOpen O)
    (h : ℝ → HermitianField M) (T C α shift : ℝ)
    (B : ℝ → DirichletEnergy g μ hμ O →L[ℝ] EnergyDual (DirichletEnergy g μ hμ O))
    (hForm : IntrinsicFormBinding g.form μ O h T C α shift
      (dirichletL2 g μ hμ O) (energyRepresentative g μ hμ O) B)
    (t : ℝ) (ht : t ∈ Icc 0 T) (f v : dirichletCore g μ hμ O) :
    B t (dirichletCoreEmbedding g μ hμ O f) (dirichletCoreEmbedding g μ hμ O v) =
      -(∫ x in O, v.val x * laplacian (h t) f.val x ∂μ) := by
  have hf : Yau.HeatConcreteBindings.ScalarTest O f.val := ⟨f.val.2.1, f.val.2.2, f.property⟩
  have hv : Yau.HeatConcreteBindings.ScalarTest O v.val := ⟨v.val.2.1, v.val.2.2, v.property⟩
  obtain ⟨_hfL, df, _hdfs, hdf, hfc⟩ := scalarTest_energyClosure g μ hμ O f.val hf
  obtain ⟨_hvL, dv, _hdvs, hdv, hvc⟩ := scalarTest_energyClosure g μ hμ O v.val hv
  have hef : energyRepresentative g μ hμ O f.val df = dirichletCoreEmbedding g μ hμ O f := by
    rw [scalarExterior_unique f.val.2.1 hdf]
    exact energyRepresentative_core g hK μ hμ O hO.measurableSet f
  have hev : energyRepresentative g μ hμ O v.val dv = dirichletCoreEmbedding g μ hμ O v := by
    rw [scalarExterior_unique v.val.2.1 hdv]
    exact energyRepresentative_core g hK μ hμ O hO.measurableSet v
  have he := ((hForm.2.2.2.2 t ht).2.2 f.val df v.val dv hf hv hdf hdv hfc hvc).2
  rw [hef, hev] at he
  exact he

/-- The actual nonsymmetric fixed-volume form admits the genuine supported
 positive-part test on every original closed-slab time. -/
theorem intrinsicForm_posPart_test
    (g : SmoothMetric M) (hK : IsKahler g) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) (hO : IsOpen O)
    (h : ℝ → HermitianField M) (T C α shift : ℝ)
    (B : ℝ → DirichletEnergy g μ hμ O →L[ℝ] EnergyDual (DirichletEnergy g μ hμ O))
    (hForm : IntrinsicFormBinding g.form μ O h T C α shift
      (dirichletL2 g μ hμ O) (energyRepresentative g μ hμ O) B)
    (t : ℝ) (ht : t ∈ Icc 0 T) (u : DirichletEnergy g μ hμ O) :
    B t u (dirichletPosPart g μ hμ O hO.measurableSet u) =
      B t (dirichletPosPart g μ hμ O hO.measurableSet u) (dirichletPosPart g μ hμ O hO.measurableSet u) := by
  exact localCoreForm_posPart_test g hK μ hμ O hO.measurableSet (h t) (B t)
    (intrinsicForm_core_formula g hK μ hμ O hO h T C α shift B hForm t ht) u

end Yau.F04Proof
