import Yau.Proofs.D03GermNoetherian
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Topology.Algebra.Module.FiniteDimension

noncomputable section

open Filter Topology

namespace Yau.Proofs.D03Aux

/-- A derivative of an analytic germ, independent of its representative. -/
def germDerivative (j : ℕ) (g : AnalyticGerm) : ℂ :=
  iteratedDeriv j (analyticRepresentative g) 0

@[simp]
theorem germDerivative_ofAnalytic (j : ℕ) (f : ℂ → ℂ) (hf : AnalyticAt ℂ f 0) :
    germDerivative j (ofAnalytic f hf) = iteratedDeriv j f 0 := by
  apply Filter.EventuallyEq.iteratedDeriv_eq j
  exact (ofAnalytic_eq_iff _ _).mp (ofAnalytic_representative _)

theorem germDerivative_add (j : ℕ) (g h : AnalyticGerm) :
    germDerivative j (g + h) = germDerivative j g + germDerivative j h := by
  have heq : g + h = ofAnalytic
      (analyticRepresentative g + analyticRepresentative h)
      ((analyticRepresentative_analytic g).add (analyticRepresentative_analytic h)) := by
    exact (congrArg₂ (· + ·) (ofAnalytic_representative g)
      (ofAnalytic_representative h)).symm
  rw [heq, germDerivative_ofAnalytic]
  exact iteratedDeriv_add (analyticRepresentative_analytic g).contDiffAt
    (analyticRepresentative_analytic h).contDiffAt

theorem germDerivative_smul (j : ℕ) (a : ℂ) (g : AnalyticGerm) :
    germDerivative j (a • g) = a • germDerivative j g := by
  have heq : a • g = ofAnalytic (fun z => a • analyticRepresentative g z)
      ((analyticRepresentative_analytic g).const_smul (c := a)) := by
    rw [Algebra.smul_def]
    exact congrArg (constantGerm a * ·) (ofAnalytic_representative g).symm
  rw [heq, germDerivative_ofAnalytic]
  exact iteratedDeriv_const_smul (analyticRepresentative_analytic g).contDiffAt a

/-- The concrete finite-dimensional space of raw derivatives of orders below k. -/
abbrev Jet (q k : ℕ) := Fin q → Fin k → ℂ

/-- Finite jets are actual complex-linear maps to a concrete Hausdorff vector space. -/
def jet (q k : ℕ) : (Fin q → AnalyticGerm) →ₗ[ℂ] Jet q k where
  toFun g i j := germDerivative j.val (g i)
  map_add' g h := by
    funext i j
    exact germDerivative_add j.val (g i) (h i)
  map_smul' a g := by
    funext i j
    exact germDerivative_smul j.val a (g i)

/-- The scalar jet kernel is exact divisibility by a power of the local coordinate. -/
theorem germ_derivatives_zero_iff (g : AnalyticGerm) (k : ℕ) :
    (∀ j < k, germDerivative j g = 0) ↔
      ∃ h : AnalyticGerm, g = zGerm ^ k * h := by
  let f := analyticRepresentative g
  have hf : AnalyticAt ℂ f 0 := analyticRepresentative_analytic g
  change (∀ j < k, iteratedDeriv j f 0 = 0) ↔ _
  rw [← natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hf,
    natCast_le_analyticOrderAt hf]
  constructor
  · rintro ⟨v, hv, hfv⟩
    refine ⟨ofAnalytic v hv, ?_⟩
    calc
      g = ofAnalytic f hf := (ofAnalytic_representative g).symm
      _ = ofAnalytic (fun z => z ^ k * v z) ((analyticAt_id.pow k).mul hv) := by
        apply (ofAnalytic_eq_iff _ _).mpr
        filter_upwards [hfv] with z hz
        simpa only [sub_zero, smul_eq_mul] using hz
      _ = zGerm ^ k * ofAnalytic v hv := rfl
  · rintro ⟨h, heq⟩
    refine ⟨analyticRepresentative h, analyticRepresentative_analytic h, ?_⟩
    have heq' : ofAnalytic f hf =
        ofAnalytic (fun z => z ^ k * analyticRepresentative h z)
          ((analyticAt_id.pow k).mul (analyticRepresentative_analytic h)) := by
      change ofAnalytic f hf = zGerm ^ k *
        ofAnalytic (analyticRepresentative h) (analyticRepresentative_analytic h)
      simpa only [f, ofAnalytic_representative] using heq
    have hfheq := (ofAnalytic_eq_iff _ _).mp heq'
    filter_upwards [hfheq] with z hz
    simpa only [sub_zero, smul_eq_mul] using hz

/-- Vanishing of a vector jet means actual coordinatewise analytic divisibility. -/
theorem jet_eq_zero_iff (q k : ℕ) (g : Fin q → AnalyticGerm) :
    jet q k g = 0 ↔ ∃ h : Fin q → AnalyticGerm, g = zGerm ^ k • h := by
  classical
  constructor
  · intro hzero
    have hcoord : ∀ i : Fin q, ∃ h : AnalyticGerm, g i = zGerm ^ k * h := by
      intro i
      apply (germ_derivatives_zero_iff (g i) k).mp
      intro j hj
      exact congrFun (congrFun hzero i) ⟨j, hj⟩
    choose h hh using hcoord
    exact ⟨h, funext hh⟩
  · rintro ⟨h, rfl⟩
    funext i j
    exact (germ_derivatives_zero_iff (zGerm ^ k * h i) k).mpr ⟨h i, rfl⟩ j.val j.isLt

/-- The jet kernel is the power of the genuine maximal ideal acting on the finite free module. -/
theorem jet_eq_zero_iff_mem (q k : ℕ) (g : Fin q → AnalyticGerm) :
    jet q k g = 0 ↔
      g ∈ germMaximalIdeal ^ k • (⊤ : Submodule AnalyticGerm (Fin q → AnalyticGerm)) := by
  rw [jet_eq_zero_iff, germMaximalIdeal_eq_span, Ideal.span_singleton_pow,
    Submodule.ideal_span_singleton_smul]
  constructor
  · rintro ⟨h, rfl⟩
    exact Submodule.smul_mem_pointwise_smul h (zGerm ^ k) ⊤ Submodule.mem_top
  · intro hg
    obtain ⟨h, _, hh⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hg
    exact ⟨h, hh.symm⟩

end Yau.Proofs.D03Aux
