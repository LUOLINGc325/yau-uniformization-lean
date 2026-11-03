import Yau.Proofs.F04VariationalWeakLimit

open MeasureTheory Filter Set TopologicalSpace
open scoped Topology InnerProductSpace

noncomputable section

namespace Yau.F04Proof

variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [SeparableSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

abbrev VariationalCoefficientFamily (j : V →L[ℝ] H) :=
  ∀ m : ℕ, ℝ → EuclideanSpace ℝ (Fin (Module.finrank ℝ (variationalGalerkinPivotSpace j m)))

def VariationalGalerkinEvolution (j : V →L[ℝ] H) (hj : Function.Injective j)
    (B : ℝ → V →L[ℝ] V →L[ℝ] ℝ) (T : ℝ) (F : ℝ → H)
    (c : VariationalCoefficientFamily j) : Prop :=
  ∀ m, ContinuousOn (c m) (Icc 0 T) ∧ c m 0 = 0 ∧
    ∀ t ∈ Icc 0 T, c m t = ∫ s in (0 : ℝ)..t,
      variationalForcing j (variationalGalerkinFamily j hj m) (F s) -
      variationalMatrix (variationalGalerkinFamily j hj m) (B s) (c m s)

/-- Actual finite zero-initial form evolutions and an actual weak time-Hilbert
 limit, constructed solely from the continuous bounded coercive form. -/
theorem variational_Galerkin_weak_limit [CompleteSpace V]
    {T C α shift : ℝ} (hT : 0 < T) (hC : 0 ≤ C) (hα : 0 < α) (hshift : 0 ≤ shift)
    (j : V →L[ℝ] H) (hj : Function.Injective j)
    (B : ℝ → V →L[ℝ] V →L[ℝ] ℝ) (hB : ∀ t, ‖B t‖ ≤ C)
    (hcB : ∀ u v, Continuous (fun t => B t u v))
    (hGard : ∀ t ∈ Icc 0 T, ∀ v : V, α * ‖v‖ ^ 2 ≤ B t v v + shift * ‖j v‖ ^ 2)
    {F : ℝ → H} (hF : MemLp F 2 (volume.restrict (Ioo 0 T))) :
    ∃ c : VariationalCoefficientFamily j, VariationalGalerkinEvolution j hj B T F c ∧
    ∃ classes : ℕ → Lp V 2 (volume.restrict (Ioo 0 T)),
      (∀ m, (classes m : ℝ → V) =ᵐ[volume.restrict (Ioo 0 T)]
        (fun t => variationalReconstruction (variationalGalerkinFamily j hj m) (c m t))) ∧
    ∃ U : Lp V 2 (volume.restrict (Ioo 0 T)),
      ‖U‖ ^ 2 ≤ coerciveEnergyBound T (2 * α) (2 * shift + 1) * (∫ s in Ioo 0 T, ‖F s‖ ^ 2) ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        ∀ ℓ : Lp V 2 (volume.restrict (Ioo 0 T)) →L[ℝ] ℝ,
          Tendsto (fun k => ℓ (classes (φ k))) atTop (𝓝 (ℓ U)) := by
  have hSol (m : ℕ) : ∃ c : ℝ → EuclideanSpace ℝ
      (Fin (Module.finrank ℝ (variationalGalerkinPivotSpace j m))),
      ContinuousOn c (Icc 0 T) ∧ c 0 = 0 ∧
      (∀ t ∈ Icc 0 T, c t = ∫ s in (0 : ℝ)..t,
        variationalForcing j (variationalGalerkinFamily j hj m) (F s) -
        variationalMatrix (variationalGalerkinFamily j hj m) (B s) (c s)) ∧
      (∫ s in Ioo 0 T, ‖variationalReconstruction (variationalGalerkinFamily j hj m) (c s)‖ ^ 2) ≤
        coerciveEnergyBound T (2 * α) (2 * shift + 1) * (∫ s in Ioo 0 T, ‖F s‖ ^ 2) := by
    obtain ⟨c, hc, hc0, hcEq, _hd⟩ := variationalGalerkin_exists hT hC j
      (variationalGalerkinFamily j hj m) B hB hcB hF
    have hEnergy := (variationalGalerkin_uniform hT hC hα hshift j _
      (variationalGalerkinFamily_value_orthonormal j hj m) B hB hcB hGard hF hc hcEq).2
    exact ⟨c, hc, hc0, hcEq, hEnergy⟩
  let c : VariationalCoefficientFamily j := fun m => Classical.choose (hSol m)
  have hc (m : ℕ) := Classical.choose_spec (hSol m)
  let curves : ℕ → ℝ → V := fun m t =>
    variationalReconstruction (variationalGalerkinFamily j hj m) (c m t)
  have hCont (m : ℕ) : ContinuousOn (curves m) (Icc 0 T) :=
    (variationalReconstruction (variationalGalerkinFamily j hj m)).continuous.comp_continuousOn (hc m).1
  have hEnergy (m : ℕ) : (∫ t in Ioo 0 T, ‖curves m t‖ ^ 2) ≤
      coerciveEnergyBound T (2 * α) (2 * shift + 1) * (∫ s in Ioo 0 T, ‖F s‖ ^ 2) :=
    (hc m).2.2.2
  obtain ⟨hMem, U, hU, φ, hφ, hWeak⟩ := variational_continuous_curves_weak_limit curves hCont hEnergy
  let classes : ℕ → Lp V 2 (volume.restrict (Ioo 0 T)) := fun m => (hMem m).toLp (curves m)
  refine ⟨c, (fun m => ⟨(hc m).1, (hc m).2.1, (hc m).2.2.1⟩), classes, ?_, U, hU, φ, hφ, hWeak⟩
  intro m
  exact (hMem m).coeFn_toLp

end Yau.F04Proof
