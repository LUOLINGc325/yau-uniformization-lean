import Yau.Proofs.V04ClockDamping
import Yau.Proofs.V04WallLaplacian
import Yau.Proofs.V04ClockBoundaryWeights

/-! Both actual wall errors cancel against the same frozen raw clock.
The resulting constant precedes the index and every admissible disc. -/

open scoped Topology ContDiff
noncomputable section
namespace Yau.Blueprint.V04Proof.ClockErrorAux
open Yau Yau.Blueprint Yau.Blueprint.V03Proof Yau.Blueprint.V04Proof

variable {n q : ℕ} {X : KahlerManifold n}

def baseClockErrorBound (d : VariationData X q) (k : ClockData X) (C : ℝ) (j : ℕ)
    (y : CotangentPoint X.manifold) (t : ℝ) : ℝ :=
  C * Real.exp (d.rho y.1 t) * (deltaBase d j y.1 ^ 3)⁻¹ *
    (if clockBaseCutoff d k j y.1 = 1 then 1 else 0)

def fiberClockErrorBound (d : VariationData X q) (k : ClockData X) (j : ℕ)
    (y : CotangentPoint X.manifold) : ℝ :=
  k.fiberCoefficient j * (1 + d.B j) ^ k.fiberPower * (wallProduct d j y ^ k.fiberPower)⁻¹ *
    (if clockFiberCutoff d k j y = 1 then 1 else 0)

def clockBoundaryDensity (d : VariationData X q) (k : ClockData X) (j a : ℕ)
    (F : VariationDisc X) (θ : ℝ) : ℝ :=
  let y := F.f (circlePoint θ)
  let t := discTime F (circlePoint θ)
  t / F.s * clockWeight d k j a F θ *
    (derivWithin (fun τ => dualNorm (d.h τ) y.1 y.2) (Set.Ici 0) t +
      derivWithin (baseCost d j y.1) (Set.Ici 0) t) + wallBase d j y.1 + wallFiber d j y

theorem clock_raw_wall_errors_bound {d : VariationData X q} (hd : VariationSetup d)
    {k : ClockData X} (hk : ClockCutoffs d k) {a : ℕ}
    (ha : 3 ≤ 4 * a) (hpa : k.fiberPower ≤ 4 * a) (hpc : k.fiberPower ≤ k.dampingPower)
    {C : ℝ} (hC : 0 ≤ C) {j : ℕ} {F : VariationDisc X}
    (hF : AdmissibleVariationDisc d j F) (θ : ℝ) :
    clockWeightRaw d k j a F θ *
      ((1 + F.s) * baseClockErrorBound d k C j (F.f (circlePoint θ)) (discTime F (circlePoint θ)) +
        fiberClockErrorBound d k j (F.f (circlePoint θ))) ≤
      ((1 + d.T) * C + 1) * ((j + 3 : ℝ) ^ k.dampingPower)⁻¹ := by
  have hJ : 0 ≤ ((j + 3 : ℝ) ^ k.dampingPower)⁻¹ := by positivity
  have hb : clockWeightRaw d k j a F θ *
      baseClockErrorBound d k C j (F.f (circlePoint θ)) (discTime F (circlePoint θ)) ≤
        C * ((j + 3 : ℝ) ^ k.dampingPower)⁻¹ := by
    by_cases hχ : clockBaseCutoff d k j (F.f (circlePoint θ)).1 = 1
    · have hh := clockRaw_base_damping hd hk ha hF θ hχ
      simp only [baseClockErrorBound, hχ, if_true, mul_one]
      convert mul_le_mul_of_nonneg_left hh hC using 1 <;> ring
    · simp only [baseClockErrorBound, hχ, if_false, mul_zero]
      exact mul_nonneg hC hJ
  have hf : clockWeightRaw d k j a F θ * fiberClockErrorBound d k j (F.f (circlePoint θ)) ≤
      ((j + 3 : ℝ) ^ k.dampingPower)⁻¹ := by
    by_cases hχ : clockFiberCutoff d k j (F.f (circlePoint θ)) = 1
    · have hh := clockRaw_fiber_damping hd hk hpa hpc hF θ hχ
      simp only [fiberClockErrorBound, hχ, if_true, mul_one]
      convert hh using 1 <;> ring
    · simp only [fiberClockErrorBound, hχ, if_false, mul_zero]
      exact hJ
  calc
    _ = (1 + F.s) * (clockWeightRaw d k j a F θ *
      baseClockErrorBound d k C j (F.f (circlePoint θ)) (discTime F (circlePoint θ))) +
        clockWeightRaw d k j a F θ * fiberClockErrorBound d k j (F.f (circlePoint θ)) := by ring
    _ ≤ (1 + F.s) * (C * ((j + 3 : ℝ) ^ k.dampingPower)⁻¹) +
        ((j + 3 : ℝ) ^ k.dampingPower)⁻¹ :=
      add_le_add (mul_le_mul_of_nonneg_left hb (by linarith [hF.2.2.2.1])) hf
    _ ≤ (1 + d.T) * (C * ((j + 3 : ℝ) ^ k.dampingPower)⁻¹) +
        ((j + 3 : ℝ) ^ k.dampingPower)⁻¹ :=
      add_le_add (mul_le_mul_of_nonneg_right (by linarith [hF.2.2.2.2.1]) (mul_nonneg hC hJ)) le_rfl
    _ = _ := by ring

theorem clockWall_pointwise_comparison {d : VariationData X q} (hd : VariationSetup d)
    {k : ClockData X} (hk : ClockCutoffs d k) (hFiber : FiberWallError d k) (hBase : BaseWallError d k)
    {a : ℕ} (ha : 3 ≤ 4 * a) (hpa : k.fiberPower ≤ 4 * a) (hpc : k.fiberPower ≤ k.dampingPower) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (j : ℕ) (F : VariationDisc X), AdmissibleVariationDisc d j F →
      ∀ θ, discTime F (circlePoint θ) / F.s * clockWeight d k j a F θ *
        symplecticP (boundaryHessian d j F (circlePoint θ)) ≤
      clockBoundaryDensity d k j a F θ +
        C * ((j + 3 : ℝ) ^ k.dampingPower)⁻¹ / circleAverage (clockWeightRaw d k j a F) := by
  obtain ⟨C₀, hC₀, hbase⟩ := hBase
  obtain ⟨s₀, hs₀, hsbound⟩ := setup_center_time_lower hd
  let R := d.T / s₀
  let A := (1 + d.T) * C₀ + 1
  have hR : 0 ≤ R := div_nonneg hd.1.le hs₀.le
  have hT : 0 ≤ d.T := hd.1.le
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  refine ⟨R * A, mul_nonneg hR hA, fun j F hF θ => ?_⟩
  let y := F.f (circlePoint θ)
  let t := discTime F (circlePoint θ)
  let E₁ := baseClockErrorBound d k C₀ j y t
  let E₂ := fiberClockErrorBound d k j y
  let Z := circleAverage (clockWeightRaw d k j a F)
  let w := t / F.s * clockWeight d k j a F θ
  have ht := admissible_discTime_mem hF (circlePoint_mem_closedBall θ)
  have hy : y ∈ boundaryRegion d j := hF.2.2.2.2.2.2.2.1 θ
  have hδ : 0 < deltaBase d j y.1 := deltaBase_pos (setup_wallProfiles hd) (setup_index_bounds hd j).1 hy.1
  have hW : 0 < wallProduct d j y := (admissible_wallProduct_bounds hd hF θ).1
  have hCoef : 0 < k.fiberCoefficient j := lt_of_lt_of_le zero_lt_one (hk.2.2.2.1 j).1
  have hB : 0 < 1 + d.B j := by linarith [(setup_index_bounds hd j).2]
  have hE₁ : 0 ≤ E₁ := by dsimp only [E₁, baseClockErrorBound]; positivity
  have hE₂ : 0 ≤ E₂ := by dsimp only [E₂, fiberClockErrorBound]; positivity
  have hraw := clockWeightRaw_pos (k := k) (a := a) hd hF θ
  have hZ : 0 < Z := clockWeightRaw_average_pos hd hF (clockWeightRaw_contDiff (a := a) hd hk hF).continuous
  have hw : 0 ≤ w := mul_nonneg (div_nonneg ht.1.le hF.2.2.2.1.le) (div_pos hraw hZ).le
  have hsame : {d with B := Function.update d.B j (d.B j)} = d := by
    rw [Function.update_eq_self]
  have hFib := hFiber j (d.B j) (hd.2.2.2.2.2.2.2.2.2.2.2.2.2 j).2.1
  dsimp only at hFib
  rw [hsame] at hFib
  have hs : F.s ∈ Set.Icc d.cylinderTimeLo d.cylinderTimeHi := hF.2.2.2.2.2.1.2.2
  have herror := (le_abs_self _).trans (hFib y hy t ⟨ht.1.le, ht.2.le⟩ F.s hs)
  change symplecticP (boundaryHessian d j F (circlePoint θ)) -
    derivWithin (fun τ => dualNorm (d.h τ) y.1 y.2) (Set.Ici 0) t -
    laplacian (d.h t) (fun x => baseCost d j x t + (1 + F.s) * wallBase d j x) y.1 ≤ E₂ at herror
  rw [HeatAux.laplacian_baseCost_add_wallBase hd j y.1 ⟨ht.1.le, ht.2.le⟩ hy.1 F.s] at herror
  have hdelta := mul_le_mul_of_nonneg_left
    ((le_abs_self _).trans (hbase j y.1 t ⟨ht.1.le, ht.2.le⟩ hy.1))
    (show 0 ≤ 1 + F.s by linarith [hF.2.2.2.1])
  have hheat := HeatAux.baseCost_laplacian_le_timeDerivative hd j y.1 ⟨ht.1.le, ht.2.le⟩
  have hspatial : symplecticP (boundaryHessian d j F (circlePoint θ)) ≤
      derivWithin (fun τ => dualNorm (d.h τ) y.1 y.2) (Set.Ici 0) t +
        derivWithin (baseCost d j y.1) (Set.Ici 0) t + ((1 + F.s) * E₁ + E₂) := by
    change (1 + F.s) * laplacian (d.h t) (wallBase d j) y.1 ≤ (1 + F.s) * E₁ at hdelta
    linarith only [herror, hdelta, hheat]
  have hrawerr := clock_raw_wall_errors_bound hd hk ha hpa hpc hC₀ hF θ
  have herr0 : 0 ≤ clockWeightRaw d k j a F θ * ((1 + F.s) * E₁ + E₂) :=
    mul_nonneg hraw.le (add_nonneg (mul_nonneg (by linarith [hF.2.2.2.1]) hE₁) hE₂)
  have hratio : t / F.s ≤ R := div_le_div₀ hd.1.le ht.2.le hs₀ (hsbound hF)
  have herr := div_le_div_of_nonneg_right (mul_le_mul hratio hrawerr herr0 hR) hZ.le
  have herr' : w * ((1 + F.s) * E₁ + E₂) ≤
      (R * A) * ((j + 3 : ℝ) ^ k.dampingPower)⁻¹ / Z := by
    convert herr using 1 <;> dsimp only [w, clockWeight, A, Z] <;> ring
  have hbound := mul_le_mul_of_nonneg_left hspatial hw
  have hwb := wallBase_nonneg (setup_wallProfiles hd) hδ
  have hwf := wallFiber_nonneg (setup_wallProfiles hd)
    (deltaFiber_pos (setup_wallProfiles hd) (setup_index_bounds hd j).2 hy.2)
  change w * symplecticP (boundaryHessian d j F (circlePoint θ)) ≤
    w * (derivWithin (fun τ => dualNorm (d.h τ) y.1 y.2) (Set.Ici 0) t +
      derivWithin (baseCost d j y.1) (Set.Ici 0) t) + wallBase d j y.1 + wallFiber d j y +
        (R * A) * ((j + 3 : ℝ) ^ k.dampingPower)⁻¹ / Z
  nlinarith only [hbound, herr', hwb, hwf]

end Yau.Blueprint.V04Proof.ClockErrorAux
