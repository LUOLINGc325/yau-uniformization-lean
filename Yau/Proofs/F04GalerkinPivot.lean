import Yau.Proofs.F04GalerkinSpaces

open Filter TopologicalSpace Set
open scoped Topology InnerProductSpace

noncomputable section

namespace Yau.F04Proof

variable {V H : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [SeparableSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The actual pivot image of each finite energy span. -/
def variationalGalerkinPivotSpace (j : V →L[ℝ] H) (m : ℕ) : Submodule ℝ H :=
  (variationalGalerkinSpace V m).map j.toLinearMap

instance variationalGalerkinPivotSpace_finiteDimensional (j : V →L[ℝ] H) (m : ℕ) :
    FiniteDimensional ℝ (variationalGalerkinPivotSpace j m) := Module.Finite.map _ _

@[simp] theorem variationalGalerkinPivotSpace_zero (j : V →L[ℝ] H) :
    variationalGalerkinPivotSpace j 0 = ⊥ := by
  simp [variationalGalerkinPivotSpace]

def variationalGalerkinPivotEquiv (j : V →L[ℝ] H) (hj : Function.Injective j) (m : ℕ) :
    variationalGalerkinSpace V m ≃ₗ[ℝ] variationalGalerkinPivotSpace j m :=
  Submodule.equivMapOfInjective j.toLinearMap hj _

def variationalGalerkinPivotBasis (j : V →L[ℝ] H) (m : ℕ) :
    OrthonormalBasis (Fin (Module.finrank ℝ (variationalGalerkinPivotSpace j m))) ℝ
      (variationalGalerkinPivotSpace j m) := stdOrthonormalBasis ℝ _

def variationalGalerkinEnergyBasis (j : V →L[ℝ] H) (hj : Function.Injective j) (m : ℕ) :
    Module.Basis (Fin (Module.finrank ℝ (variationalGalerkinPivotSpace j m))) ℝ
      (variationalGalerkinSpace V m) :=
  (variationalGalerkinPivotBasis j m).toBasis.map (variationalGalerkinPivotEquiv j hj m).symm

def variationalGalerkinFamily (j : V →L[ℝ] H) (hj : Function.Injective j) (m : ℕ) :
    Fin (Module.finrank ℝ (variationalGalerkinPivotSpace j m)) → V :=
  fun k => variationalGalerkinEnergyBasis j hj m k

@[simp] theorem variationalGalerkinFamily_mem (j : V →L[ℝ] H) (hj : Function.Injective j)
    (m : ℕ) (k : Fin (Module.finrank ℝ (variationalGalerkinPivotSpace j m))) :
    variationalGalerkinFamily j hj m k ∈ variationalGalerkinSpace V m :=
  (variationalGalerkinEnergyBasis j hj m k).property

@[simp] theorem variationalGalerkinFamily_value (j : V →L[ℝ] H) (hj : Function.Injective j)
    (m : ℕ) (k : Fin (Module.finrank ℝ (variationalGalerkinPivotSpace j m))) :
    j (variationalGalerkinFamily j hj m k) = (variationalGalerkinPivotBasis j m k : H) := by
  change j ((variationalGalerkinPivotEquiv j hj m).symm (variationalGalerkinPivotBasis j m k) :
    variationalGalerkinSpace V m) = _
  exact Submodule.map_equivMapOfInjective_symm_apply _ hj _ _

theorem variationalGalerkinFamily_value_orthonormal (j : V →L[ℝ] H)
    (hj : Function.Injective j) (m : ℕ) :
    Orthonormal ℝ (fun k => j (variationalGalerkinFamily j hj m k)) := by
  simp_rw [variationalGalerkinFamily_value]
  exact (variationalGalerkinPivotBasis j m).orthonormal.comp_linearIsometry
    (variationalGalerkinPivotSpace j m).subtypeₗᵢ

theorem variationalGalerkinFamily_span (j : V →L[ℝ] H) (hj : Function.Injective j) (m : ℕ) :
    Submodule.span ℝ (Set.range (variationalGalerkinFamily j hj m)) = variationalGalerkinSpace V m := by
  change Submodule.span ℝ (Set.range (fun k =>
    (variationalGalerkinSpace V m).subtype (variationalGalerkinEnergyBasis j hj m k))) = _
  have hb := (variationalGalerkinEnergyBasis j hj m).span_eq
  apply_fun Submodule.map (variationalGalerkinSpace V m).subtype at hb
  simpa only [Submodule.map_span, ← Set.range_comp, Function.comp_def,
    Submodule.map_top, Submodule.range_subtype] using hb

/-- The initial stage has the actual empty basis, including zero-dimensional
 energy or pivot spaces. -/
@[simp] theorem variationalGalerkinPivot_finrank_zero (j : V →L[ℝ] H) :
    Module.finrank ℝ (variationalGalerkinPivotSpace j 0) = 0 := by simp

end Yau.F04Proof
