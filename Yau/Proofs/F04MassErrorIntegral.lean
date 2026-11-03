import Yau.Proofs.F04MassScalarError
import Yau.Proofs.F04MassPowers

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold

noncomputable section

namespace Yau.F04Proof

open Yau.Blueprint Yau.LeafProofs.L18Aux

/-- The error is integrated before the cutoff radius is sent to infinity.
All constants come from the supplied exhaustion and the actual rho average. -/
theorem flow_mass_error_integral {n : ℕ} (X : KahlerManifold n) (o : Pt X)
    (h : Flow X) (U P ρ : STF X) (hloc : LocalizedFlow X o h U P ρ)
    (u : Pt X → ℝ) (hu : ControlledExhaustion X o u)
    (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
    {T : ℝ} (hT : 0 < T) :
    ∃ D B : ℝ, 0 < D ∧ 0 < B ∧ ∀ (χ : Pt X → ℝ) (C : ℝ) (k : ℕ),
      0 < C → 2 * n ≤ k → SmoothFn χ →
      (∀ x, 0 < χ x) → (∀ x, χ x ≤ C * (u x) ^ (-(k : ℤ))) →
      (∀ x, gradNormSq X.metric.form χ x ≤ (C * χ x / u x) ^ 2) →
      ∀ R : ℝ, 1 ≤ R → ∀ t ∈ Icc 0 T, ∀ z : Pt X → ℝ,
        SmoothFn z → (∀ x, 0 ≤ z x ∧ z x ≤ ρ x t) →
        Integrable (fun x => |z x * massScalarError (h t) u χ R x * density ρ x t|) μ ∧
          (∫ x, |z x * massScalarError (h t) u χ R x * density ρ x t| ∂μ) ≤
            ((n : ℝ) * (D + C ^ 2 + D ^ 2) * C * B) / R := by
  obtain ⟨D, hD, hcof⟩ := mass_error_cofactor_bound X o h U P ρ hloc u hu
  obtain ⟨B, hB, hmass⟩ := flow_rho_sublevel_mass_polynomial X o h U P ρ hloc u hu μ hμ hT
  refine ⟨D, B, hD, hB, ?_⟩
  intro χ C k hC hk hχ hχpos hχupper hχgrad R hR t ht z hz hzbound
  have hRp : 0 < R := lt_of_lt_of_le zero_lt_one hR
  let E := D + C ^ 2 + D ^ 2
  let A := (n : ℝ) * E * C
  let q := A / (R ^ k * R ^ 2)
  let S : Set (Pt X) := {x | u x ≤ 2 * R}
  let f : Pt X → ℝ := fun x => |z x * massScalarError (h t) u χ R x * density ρ x t|
  have hE : 0 < E := by dsimp only [E]; positivity
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hq : 0 ≤ q := div_nonneg hA (by positivity)
  have hzero (x : Pt X) (hx : u x < R ∨ 2 * R < u x) : f x = 0 := by
    have hnot : ¬ (R ≤ u x ∧ u x ≤ 2 * R) := by
      intro hh
      rcases hx with hx | hx <;> linarith
    have he := mass_error_zero_off_shell (u := u) (χ := χ) hu.1 hRp (h t) x hnot
    dsimp only [f]
    rw [massScalarError_eq_trace (h t) hu.1 hχ R x, he, mul_zero, zero_mul, abs_zero]
  have hpoint (x : Pt X) (_hx : x ∈ S) : f x ≤ q * ρ x t := by
    by_cases hRx : R ≤ u x
    · have hχb : χ x ≤ C / R ^ k := by
        calc
          _ ≤ C * (u x) ^ (-(k : ℤ)) := hχupper x
          _ ≤ C * (1 / R ^ k) :=
            mul_le_mul_of_nonneg_left (negative_nat_power_bound hRp hRx k) hC.le
          _ = _ := by ring
      have hc := hcof χ C hχpos hχgrad R hR x t ht.1
      have he : |massScalarError (h t) u χ R x| * density ρ x t ≤ q := by
        rw [massScalarError_eq_trace (h t) hu.1 hχ R x]
        calc
          _ ≤ (n : ℝ) * (E * χ x / R ^ 2) := hc
          _ ≤ (n : ℝ) * (E * (C / R ^ k) / R ^ 2) :=
            mul_le_mul_of_nonneg_left
              (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hχb hE.le) (sq_nonneg R))
              (Nat.cast_nonneg n)
          _ = q := by
            dsimp only [q, A]
            simp only [div_eq_mul_inv, mul_inv_rev]
            ring
      dsimp only [f]
      rw [abs_mul, abs_mul, abs_of_nonneg (hzbound x).1, abs_of_pos (density_pos ρ x t)]
      calc
        _ = z x * (|massScalarError (h t) u χ R x| * density ρ x t) := by ring
        _ ≤ z x * q := mul_le_mul_of_nonneg_left he (hzbound x).1
        _ ≤ ρ x t * q := mul_le_mul_of_nonneg_right (hzbound x).2 hq
        _ = _ := mul_comm _ _
    · rw [hzero x (Or.inl (lt_of_not_ge hRx))]
      exact mul_nonneg hq (rho_nonneg o h U P ρ hloc x t ht.1)
  have hS : MeasurableSet S := (hu.2.1 (2 * R)).measurableSet
  have hgOn : IntegrableOn (fun x => q * ρ x t) S μ := (hmass R hR t ht).1.const_mul q
  have hg : Integrable (S.indicator (fun x => q * ρ x t)) μ := hgOn.integrable_indicator hS
  have hcomp : ∀ x, f x ≤ S.indicator (fun x => q * ρ x t) x := by
    intro x
    by_cases hx : x ∈ S
    · simpa only [indicator_of_mem hx] using hpoint x hx
    · rw [indicator_of_notMem hx, hzero x (Or.inr (lt_of_not_ge hx))]
  have hden : SmoothFn (fun x => density ρ x t) := by
    intro c
    exact ((hloc.2.2.2.1 c).neg.exp).comp (contDiffOn_id.prodMk contDiffOn_const)
      (fun _ hz => ⟨hz, ht.1⟩)
  have herr := massScalarError_smooth (h t)
    (metricFamilySmooth_slice h (Ici 0) hloc.1.2.1 t ht.1) hu.1 hχ R
  have hfc : Continuous f :=
    (((continuous_of_smoothFn hz).mul (continuous_of_smoothFn herr)).mul
      (continuous_of_smoothFn hden)).abs
  have hf : Integrable f μ := hg.mono' hfc.aestronglyMeasurable (ae_of_all _ (fun x => by
    simpa only [Real.norm_eq_abs, f, abs_abs] using hcomp x))
  refine ⟨hf, ?_⟩
  calc
    _ ≤ ∫ x, S.indicator (fun x => q * ρ x t) x ∂μ := integral_mono hf hg hcomp
    _ = q * ∫ x in S, ρ x t ∂μ := by rw [integral_indicator hS, integral_const_mul]
    _ ≤ q * (B * R ^ (2 * n + 1)) := mul_le_mul_of_nonneg_left (hmass R hR t ht).2 hq
    _ = (A * B) * (R ^ (2 * n + 1) / (R ^ k * R ^ 2)) := by dsimp only [q]; ring
    _ ≤ (A * B) * (1 / R) :=
      mul_le_mul_of_nonneg_left (polynomial_mass_error_decay hR hk) (mul_nonneg hA hB.le)
    _ = ((n : ℝ) * (D + C ^ 2 + D ^ 2) * C * B) / R := by dsimp only [A, E]; ring

end Yau.F04Proof
