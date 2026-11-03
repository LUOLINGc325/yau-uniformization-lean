import Yau.Proofs.F04TimeBilinear
import Yau.LeafProofs.L16EnergyTimeForm

open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal

noncomputable section

namespace Yau.F04Proof

open Yau.LeafProofs.L16Aux

variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Scalar time tests give genuine energy-valued Bochner tests. -/
theorem memLp_scalar_vector {ν : Measure ℝ} {η : ℝ → ℝ} (hη : MemLp η 2 ν) (v : V) :
    MemLp (fun t => η t • v) 2 ν := by
  exact hη.continuousLinearMap_comp ((ContinuousLinearMap.id ℝ ℝ).smulRight v)

def scalarTimeVector {ν : Measure ℝ} {η : ℝ → ℝ} (hη : MemLp η 2 ν) (v : V) : Lp V 2 ν :=
  (memLp_scalar_vector hη v).toLp (fun t => η t • v)

theorem scalarTimeVector_coeFn {ν : Measure ℝ} {η : ℝ → ℝ} (hη : MemLp η 2 ν) (v : V) :
    scalarTimeVector hη v =ᵐ[ν] (fun t => η t • v) :=
  (memLp_scalar_vector hη v).coeFn_toLp

variable (B : ℝ → V →L[ℝ] V →L[ℝ] ℝ) (C : ℝ) (hC : 0 ≤ C)
  (hB : ∀ t, ‖B t‖ ≤ C) (hc : ∀ u v, Continuous (fun t => B t u v))
  (ν : Measure ℝ)

include hB hc in
theorem variationalTimeForm_integrable {η : ℝ → ℝ} (hη : MemLp η 2 ν)
    (v : V) {U : ℝ → V} (hU : MemLp U 2 ν) :
    Integrable (fun t => η t * B t (U t) v) ν := by
  simpa only [map_smul, smul_eq_mul] using
    bounded_bilinear_time_integrable B C hB hc ν hU (memLp_scalar_vector hη v)

def variationalFixedTimeForm {η : ℝ → ℝ} (hη : MemLp η 2 ν) (v : V) :
    Lp V 2 ν →L[ℝ] ℝ :=
  (variationalTimeBilinear B C hC hB hc ν).flip (scalarTimeVector hη v)

theorem variationalFixedTimeForm_apply {η : ℝ → ℝ} (hη : MemLp η 2 ν) (v : V)
    (U : Lp V 2 ν) :
    variationalFixedTimeForm B C hC hB hc ν hη v U = ∫ t, η t * B t (U t) v ∂ν := by
  change variationalTimeBilinear B C hC hB hc ν U (scalarTimeVector hη v) = _
  rw [variationalTimeBilinear_apply]
  apply integral_congr_ae
  filter_upwards [scalarTimeVector_coeFn hη v] with t ht
  rw [ht, map_smul, smul_eq_mul]

/-- This is an actual continuous linear functional of the time L2 class,
 retaining the initial face through the permitted terminal-zero test. -/
def variationalWeakTimeFunctional (j : V →L[ℝ] H) {η : ℝ → ℝ}
    (hη : MemLp η 2 ν) (hηD : MemLp (deriv η) 2 ν) (v : V) :
    Lp V 2 ν →L[ℝ] ℝ :=
  -timeTestFunctional hηD ((innerSL ℝ (j v)).comp j) +
    variationalFixedTimeForm B C hC hB hc ν hη v

theorem variationalWeakTimeFunctional_apply (j : V →L[ℝ] H) {η : ℝ → ℝ}
    (hη : MemLp η 2 ν) (hηD : MemLp (deriv η) 2 ν) (v : V) (U : Lp V 2 ν) :
    variationalWeakTimeFunctional B C hC hB hc ν j hη hηD v U =
      ∫ t, -deriv η t * inner ℝ (j (U t)) (j v) + η t * B t (U t) v ∂ν := by
  let L := (innerSL ℝ (j v)).comp j
  have hi : Integrable (fun t => deriv η t * inner ℝ (j v) (j (U t))) ν := by
    simpa only [L, ContinuousLinearMap.comp_apply, innerSL_apply_apply] using
      timeTestFunctional_integrable hηD L (Lp.memLp U)
  have hb := variationalTimeForm_integrable B C hB hc ν hη v (Lp.memLp U)
  rw [variationalWeakTimeFunctional, add_apply, neg_apply,
    timeTestFunctional_apply, variationalFixedTimeForm_apply]
  simp only [ContinuousLinearMap.comp_apply, innerSL_apply_apply]
  symm
  calc
    _ = ∫ t, -(deriv η t * inner ℝ (j v) (j (U t))) + η t * B t (U t) v ∂ν := by
      congr 1
      funext t
      rw [real_inner_comm]
      ring
    _ = (∫ t, -(deriv η t * inner ℝ (j v) (j (U t))) ∂ν) +
        ∫ t, η t * B t (U t) v ∂ν := integral_add hi.neg hb
    _ = _ := by rw [integral_neg]

end Yau.F04Proof
