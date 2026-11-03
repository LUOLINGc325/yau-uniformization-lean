import Yau.Proofs.P06HodgeRegularityWeakJets

/-! Actual weak derivatives and finite jets under a measure-preserving
continuous linear equivalence, including the true transformed directions. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff

namespace Yau.NodeProofs.P06Aux

variable {E F ι κ α : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F]

theorem regularityWeakDeriv_transport
    (μ : Measure E) (ν : Measure F) (e : E ≃L[ℝ] F) (he : MeasurePreserving e μ ν)
    (d : E) (u du : E → ℝ) (h : regularityWeakDeriv μ Set.univ d u du) :
    regularityWeakDeriv ν Set.univ (e d) (fun y => u (e.symm y)) (fun y => du (e.symm y)) := by
  intro φ hφ
  have hψ : regularityTest Set.univ (fun z => φ (e z)) :=
    ⟨hφ.1.comp e.contDiff,hφ.2.1.comp_homeomorph e.toHomeomorph,Set.subset_univ _⟩
  have hh := h (fun z => φ (e z)) hψ
  simp only [Measure.restrict_univ] at hh ⊢
  have hd (z : E) : fderiv ℝ (fun x => φ (e x)) z d = fderiv ℝ φ (e z) (e d) := by
    have hc := ((hφ.1.differentiable (by simp) (e z)).hasFDerivAt.comp z e.hasFDerivAt).fderiv
    exact DFunLike.congr_fun hc d
  simp_rw [hd] at hh
  have hI := he.integral_comp e.toHomeomorph.measurableEmbedding
    (fun y => u (e.symm y) * fderiv ℝ φ y (e d))
  have hJ := he.integral_comp e.toHomeomorph.measurableEmbedding
    (fun y => du (e.symm y) * φ y)
  simp only [e.symm_apply_apply] at hI hJ
  rw [← hI,← hJ]
  exact hh

theorem regularityWeakJet_transport
    (μ : Measure E) (ν : Measure F) (e : E ≃L[ℝ] F) (he : MeasurePreserving e μ ν)
    (v : ι → E) (w : κ → F) (index : κ → ι) (hdir : ∀ i, e (v (index i)) = w i)
    (s : ℕ) (U : E → α → ℝ) (J : List ι → E → α → ℝ)
    (hJ : regularityWeakJet μ Set.univ v s U J) :
    regularityWeakJet ν Set.univ w s (fun y c => U (e.symm y) c)
      (fun a y c => J (a.map index) (e.symm y) c) := by
  have he' : MeasurePreserving e.symm ν μ :=
    MeasurePreserving.symm e.toHomeomorph.toMeasurableEquiv he
  refine ⟨?_,?_,?_⟩
  · funext y c
    change J [] (e.symm y) c = U (e.symm y) c
    rw [hJ.1]
  · intro a ha c
    have hLp : MemLp (fun z => J (a.map index) z c) 2 μ := by
      simpa only [Measure.restrict_univ] using hJ.2.1 (a.map index) (by simpa only [List.length_map] using ha) c
    simpa only [Measure.restrict_univ,Function.comp_def] using hLp.comp_measurePreserving he'
  · intro a ha i c
    have hw := regularityWeakDeriv_transport μ ν e he (v (index i))
      (fun z => J (a.map index) z c) (fun z => J (index i :: a.map index) z c)
      (hJ.2.2 (a.map index) (by simpa only [List.length_map] using ha) (index i) c)
    simpa only [hdir i,List.map_cons] using hw

end Yau.NodeProofs.P06Aux
