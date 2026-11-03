import Yau.LeafProofs.L16EnergyGraph
import Yau.LeafProofs.L16EnergyEquation
import Mathlib.MeasureTheory.Function.Holder

/-! The actual fixed-time variational form on the closed spatial energy graph.
The bounds below are explicit intermediate coefficient hypotheses. No deduction
of these bounds from smooth coefficients, and no existence theorem, is asserted. -/
open MeasureTheory Filter
open scoped Topology
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic

variable {n : ℕ}

/-- The literal divergence-form energy integral, using actual graph coordinates. -/
def energyFormValue (O : Set (Space n)) (a : Point n → Mat n)
    (b : Point n → Yau.RIdx n → ℝ) (t : ℝ) (v w : EnergyGraphSpace O) : ℝ :=
  ∫ x in O, (∑ i, ∑ j, a (x,t) i j * energyGradientProjection O j v x *
    energyGradientProjection O i w x) -
    ∑ j, energyDrift a b (x,t) j * energyGradientProjection O j v x *
      energyValueProjection O w x

/-- All assumptions refer to the actual coefficient and its actual derivative drift. -/
def EnergySliceBounds (O : Set (Space n)) (a : Point n → Mat n)
    (b : Point n → Yau.RIdx n → ℝ) (t A D : ℝ) : Prop :=
  0 ≤ A ∧ 0 ≤ D ∧
  (∀ i j, AEStronglyMeasurable (fun x => a (x,t) i j) (volume.restrict O)) ∧
  (∀ j, AEStronglyMeasurable (fun x => energyDrift a b (x,t) j) (volume.restrict O)) ∧
  (∀ i j, ∀ᵐ x ∂volume.restrict O, |a (x,t) i j| ≤ A) ∧
  (∀ᵐ x ∂volume.restrict O, (∑ j, |energyDrift a b (x,t) j|^2) ≤ D^2)

private theorem drift_component_bound {ι : Type*} [Fintype ι] (c : ι → ℝ)
    {D : ℝ} (hD : 0 ≤ D) (h : (∑ j, |c j|^2) ≤ D^2) (j : ι) : |c j| ≤ D := by
  have hj : |c j|^2 ≤ ∑ k, |c k|^2 := Finset.single_le_sum (fun k _ => sq_nonneg |c k|) (Finset.mem_univ j)
  nlinarith [abs_nonneg (c j)]

theorem EnergySliceBounds.principal_memLp {O : Set (Space n)}
    {a : Point n → Mat n} {b : Point n → Yau.RIdx n → ℝ} {t A D : ℝ}
    (h : EnergySliceBounds O a b t A D) (i j : Yau.RIdx n) :
    MemLp (fun x => a (x,t) i j) ⊤ (volume.restrict O) :=
  memLp_top_of_bound (h.2.2.1 i j) A (by simpa only [Real.norm_eq_abs] using h.2.2.2.2.1 i j)

theorem EnergySliceBounds.drift_bound {O : Set (Space n)}
    {a : Point n → Mat n} {b : Point n → Yau.RIdx n → ℝ} {t A D : ℝ}
    (h : EnergySliceBounds O a b t A D) (j : Yau.RIdx n) :
    ∀ᵐ x ∂volume.restrict O, |energyDrift a b (x,t) j| ≤ D :=
  h.2.2.2.2.2.mono fun _ hx => drift_component_bound _ h.2.1 hx j

theorem EnergySliceBounds.drift_memLp {O : Set (Space n)}
    {a : Point n → Mat n} {b : Point n → Yau.RIdx n → ℝ} {t A D : ℝ}
    (h : EnergySliceBounds O a b t A D) (j : Yau.RIdx n) :
    MemLp (fun x => energyDrift a b (x,t) j) ⊤ (volume.restrict O) :=
  memLp_top_of_bound (h.2.2.2.1 j) D (by simpa only [Real.norm_eq_abs] using h.drift_bound j)

private def weightedL2Pair {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {η : α → ℝ} (hη : MemLp η ⊤ μ) : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ →L[ℝ] ℝ :=
  (innerSL ℝ).bilinearComp
    ((ContinuousLinearMap.mul ℝ ℝ).holderL μ ⊤ 2 2 (hη.toLp η))
    (ContinuousLinearMap.id ℝ _)

private theorem weightedL2Pair_apply {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {η : α → ℝ} (hη : MemLp η ⊤ μ) (u v : Lp ℝ 2 μ) :
    weightedL2Pair hη u v = ∫ x, η x * u x * v x ∂μ := by
  rw [weightedL2Pair, ContinuousLinearMap.bilinearComp_apply, innerSL_apply_apply, L2.inner_def]
  apply integral_congr_ae
  have hm := (ContinuousLinearMap.mul ℝ ℝ).coeFn_holder (hη.toLp η) u (r := 2)
  filter_upwards [hm, hη.coeFn_toLp] with x hx hηx
  simp only [ContinuousLinearMap.holderL_apply_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.mul_apply', hηx] at hx ⊢
  rw [hx]
  simp only [RCLike.inner_apply, conj_trivial]
  ring

private theorem weightedL2Pair_bound {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {η : α → ℝ} (hη : MemLp η ⊤ μ) {C : ℝ} (hC : 0 ≤ C)
    (hηC : ∀ᵐ x ∂μ, |η x| ≤ C) (u v : Lp ℝ 2 μ) :
    ‖weightedL2Pair hη u v‖ ≤ C * ‖u‖ * ‖v‖ := by
  have hηn : ‖hη.toLp η‖ ≤ C := by
    rw [Lp.norm_toLp, eLpNorm_exponent_top hη.aestronglyMeasurable]
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top
      (eLpNormEssSup_le_of_ae_bound (by simpa only [Real.norm_eq_abs] using hηC))).trans_eq
      (ENNReal.toReal_ofReal hC)
  change ‖innerSL ℝ ((ContinuousLinearMap.mul ℝ ℝ).holder 2 (hη.toLp η) u) v‖ ≤ _
  calc
    _ ≤ ‖(ContinuousLinearMap.mul ℝ ℝ).holder 2 (hη.toLp η) u‖ * ‖v‖ := norm_inner_le_norm _ _
    _ ≤ (‖ContinuousLinearMap.mul ℝ ℝ‖ * ‖hη.toLp η‖ * ‖u‖) * ‖v‖ :=
      mul_le_mul_of_nonneg_right (ContinuousLinearMap.norm_holder_apply_apply_le _ _ _) (norm_nonneg _)
    _ ≤ C * ‖u‖ * ‖v‖ := by
      gcongr
      calc
        ‖ContinuousLinearMap.mul ℝ ℝ‖ * ‖hη.toLp η‖ ≤ 1 * C :=
          mul_le_mul (ContinuousLinearMap.opNorm_mul_le ℝ ℝ) hηn (norm_nonneg _) zero_le_one
        _ = C := one_mul _

/-- Exact square-sum identity of the actual Hilbert graph norm. -/
theorem energyGraphSpace_norm_sq (O : Set (Space n)) (v : EnergyGraphSpace O) :
    ‖v‖^2 = ‖energyValueProjection O v‖^2 + ∑ i, ‖energyGradientProjection O i v‖^2 := by
  change ‖v.1‖^2 = _
  rw [PiLp.norm_sq_eq_of_L2, Fintype.sum_option]
  rfl

/-- Each principal summand is an honest integrable weighted `L²` product. -/
theorem energyForm_principal_integrable {O : Set (Space n)}
    {a : Point n → Mat n} {b : Point n → Yau.RIdx n → ℝ} {t A D : ℝ}
    (h : EnergySliceBounds O a b t A D) (v w : EnergyGraphSpace O) (i j : Yau.RIdx n) :
    Integrable (fun x => a (x,t) i j * energyGradientProjection O j v x *
      energyGradientProjection O i w x) (volume.restrict O) :=
by
  have hm : MemLp (fun x => a (x,t) i j * energyGradientProjection O j v x) 2 (volume.restrict O) :=
    (h.principal_memLp i j).mul (Lp.memLp _)
  exact hm.integrable_mul (Lp.memLp _)

/-- Each actual drift summand is an honest integrable weighted `L²` product. -/
theorem energyForm_drift_integrable {O : Set (Space n)}
    {a : Point n → Mat n} {b : Point n → Yau.RIdx n → ℝ} {t A D : ℝ}
    (h : EnergySliceBounds O a b t A D) (v w : EnergyGraphSpace O) (j : Yau.RIdx n) :
    Integrable (fun x => energyDrift a b (x,t) j * energyGradientProjection O j v x *
      energyValueProjection O w x) (volume.restrict O) :=
by
  have hm : MemLp (fun x => energyDrift a b (x,t) j * energyGradientProjection O j v x) 2 (volume.restrict O) :=
    (h.drift_memLp j).mul (Lp.memLp _)
  exact hm.integrable_mul (Lp.memLp _)

/-- The entire actual integrand is integrable. -/
theorem energyForm_integrable {O : Set (Space n)}
    {a : Point n → Mat n} {b : Point n → Yau.RIdx n → ℝ} {t A D : ℝ}
    (h : EnergySliceBounds O a b t A D) (v w : EnergyGraphSpace O) :
    Integrable (fun x => (∑ i, ∑ j, a (x,t) i j * energyGradientProjection O j v x *
      energyGradientProjection O i w x) -
      ∑ j, energyDrift a b (x,t) j * energyGradientProjection O j v x *
        energyValueProjection O w x) (volume.restrict O) :=
  (integrable_finsetSum _ fun i _ =>
    integrable_finsetSum _ fun j _ => energyForm_principal_integrable h v w i j).sub
    (integrable_finsetSum _ fun j _ => energyForm_drift_integrable h v w j)

/-- A genuine continuous bilinear form, constructed from actual coefficient multiplication. -/
def energyForm {O : Set (Space n)} {a : Point n → Mat n}
    {b : Point n → Yau.RIdx n → ℝ} {t A D : ℝ}
    (h : EnergySliceBounds O a b t A D) :
    EnergyGraphSpace O →L[ℝ] EnergyGraphSpace O →L[ℝ] ℝ :=
  (∑ i, ∑ j, (weightedL2Pair (h.principal_memLp i j)).bilinearComp
    (energyGradientProjection O j) (energyGradientProjection O i)) -
  ∑ j, (weightedL2Pair (h.drift_memLp j)).bilinearComp
    (energyGradientProjection O j) (energyValueProjection O)

/-- The bundled form evaluates to the literal actual-coefficient integral. -/
theorem energyForm_apply {O : Set (Space n)} {a : Point n → Mat n}
    {b : Point n → Yau.RIdx n → ℝ} {t A D : ℝ}
    (h : EnergySliceBounds O a b t A D) (v w : EnergyGraphSpace O) :
    energyForm h v w = energyFormValue O a b t v w := by
  simp only [energyForm, sub_apply, sum_apply,
    ContinuousLinearMap.bilinearComp_apply, weightedL2Pair_apply, energyFormValue]
  rw [integral_sub
    (integrable_finsetSum _ fun i _ =>
      integrable_finsetSum _ fun j _ => energyForm_principal_integrable h v w i j)
    (integrable_finsetSum _ fun j _ => energyForm_drift_integrable h v w j)]
  congr 1
  · rw [integral_finsetSum _ fun i _ =>
      integrable_finsetSum _ fun j _ => energyForm_principal_integrable h v w i j]
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_finsetSum _ fun j _ => energyForm_principal_integrable h v w i j]
  · rw [integral_finsetSum _ fun j _ => energyForm_drift_integrable h v w j]

/-- Integral bilinearity follows through the genuine `Lp` quotient operations. -/
theorem energyFormValue_add_left {O : Set (Space n)} {a : Point n → Mat n}
    {b : Point n → Yau.RIdx n → ℝ} {t A D : ℝ}
    (h : EnergySliceBounds O a b t A D) (u v w : EnergyGraphSpace O) :
    energyFormValue O a b t (u+v) w = energyFormValue O a b t u w + energyFormValue O a b t v w := by
  simpa only [energyForm_apply, add_apply] using
    congrArg (fun L : EnergyGraphSpace O →L[ℝ] ℝ => L w) ((energyForm h).map_add u v)

theorem energyFormValue_add_right {O : Set (Space n)} {a : Point n → Mat n}
    {b : Point n → Yau.RIdx n → ℝ} {t A D : ℝ}
    (h : EnergySliceBounds O a b t A D) (u v w : EnergyGraphSpace O) :
    energyFormValue O a b t u (v+w) = energyFormValue O a b t u v + energyFormValue O a b t u w := by
  simpa only [energyForm_apply] using (energyForm h u).map_add v w

theorem energyFormValue_smul_left {O : Set (Space n)} {a : Point n → Mat n}
    {b : Point n → Yau.RIdx n → ℝ} {t A D : ℝ}
    (h : EnergySliceBounds O a b t A D) (c : ℝ) (v w : EnergyGraphSpace O) :
    energyFormValue O a b t (c • v) w = c * energyFormValue O a b t v w := by
  simpa only [energyForm_apply, smul_apply, smul_eq_mul] using
    congrArg (fun L : EnergyGraphSpace O →L[ℝ] ℝ => L w) ((energyForm h).map_smul c v)

theorem energyFormValue_smul_right {O : Set (Space n)} {a : Point n → Mat n}
    {b : Point n → Yau.RIdx n → ℝ} {t A D : ℝ}
    (h : EnergySliceBounds O a b t A D) (c : ℝ) (v w : EnergyGraphSpace O) :
    energyFormValue O a b t v (c • w) = c * energyFormValue O a b t v w := by
  simpa only [energyForm_apply, smul_eq_mul] using (energyForm h v).map_smul c w

private theorem energyCoordinateProjection_apply_bound (O : Set (Space n))
    (k : Option (Yau.RIdx n)) (v : EnergyGraphSpace O) :
    ‖energyCoordinateProjection O k v‖ ≤ ‖v‖ := by
  calc
    _ ≤ ‖energyCoordinateProjection O k‖ * ‖v‖ := (energyCoordinateProjection O k).le_opNorm v
    _ ≤ 1 * ‖v‖ := mul_le_mul_of_nonneg_right (energyCoordinateProjection_norm_le O k) (norm_nonneg _)
    _ = ‖v‖ := one_mul _

/-- A positive form bound fixed before either input vector or any forcing. -/
def energyFormBound (n : ℕ) (A D : ℝ) : ℝ :=
  1 + (Fintype.card (Yau.RIdx n) : ℝ)^2 * A + (Fintype.card (Yau.RIdx n) : ℝ) * D

theorem energyFormBound_pos {A D : ℝ} (hA : 0 ≤ A) (hD : 0 ≤ D) :
    0 < energyFormBound n A D := by
  unfold energyFormBound
  positivity

theorem energyForm_apply_bound {O : Set (Space n)} {a : Point n → Mat n}
    {b : Point n → Yau.RIdx n → ℝ} {t A D : ℝ}
    (h : EnergySliceBounds O a b t A D) (v w : EnergyGraphSpace O) :
    ‖energyForm h v w‖ ≤ energyFormBound n A D * ‖v‖ * ‖w‖ := by
  have hp (i j : Yau.RIdx n) :
      ‖weightedL2Pair (h.principal_memLp i j)
        (energyGradientProjection O j v) (energyGradientProjection O i w)‖ ≤ A * ‖v‖ * ‖w‖ := by
    calc
      _ ≤ A * ‖energyGradientProjection O j v‖ * ‖energyGradientProjection O i w‖ :=
        weightedL2Pair_bound _ h.1 (h.2.2.2.2.1 i j) _ _
      _ ≤ A * ‖v‖ * ‖w‖ := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left (energyCoordinateProjection_apply_bound O (some j) v) h.1)
          (energyCoordinateProjection_apply_bound O (some i) w) (norm_nonneg _)
          (mul_nonneg h.1 (norm_nonneg _))
  have hd (j : Yau.RIdx n) :
      ‖weightedL2Pair (h.drift_memLp j)
        (energyGradientProjection O j v) (energyValueProjection O w)‖ ≤ D * ‖v‖ * ‖w‖ := by
    calc
      _ ≤ D * ‖energyGradientProjection O j v‖ * ‖energyValueProjection O w‖ :=
        weightedL2Pair_bound _ h.2.1 (h.drift_bound j) _ _
      _ ≤ D * ‖v‖ * ‖w‖ := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left (energyCoordinateProjection_apply_bound O (some j) v) h.2.1)
          (energyCoordinateProjection_apply_bound O none w) (norm_nonneg _)
          (mul_nonneg h.2.1 (norm_nonneg _))
  simp only [energyForm, sub_apply, sum_apply,
    ContinuousLinearMap.bilinearComp_apply]
  calc
    _ ≤ ‖∑ i, ∑ j, weightedL2Pair (h.principal_memLp i j)
      (energyGradientProjection O j v) (energyGradientProjection O i w)‖ +
      ‖∑ j, weightedL2Pair (h.drift_memLp j)
        (energyGradientProjection O j v) (energyValueProjection O w)‖ := norm_sub_le _ _
    _ ≤ (∑ i : Yau.RIdx n, ∑ j : Yau.RIdx n, A * ‖v‖ * ‖w‖) +
      ∑ j : Yau.RIdx n, D * ‖v‖ * ‖w‖ := by
      apply add_le_add
      · exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ =>
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => hp i j))
      · exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => hd j)
    _ ≤ energyFormBound n A D * ‖v‖ * ‖w‖ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      unfold energyFormBound
      nlinarith [mul_nonneg (norm_nonneg v) (norm_nonneg w)]

/-- The canonical operator norm, with scalar fields explicit so instance
resolution does not lose them through the closed-submodule coercion. -/
instance energyGraphBilinearForm_norm (O : Set (Space n)) :
    Norm (EnergyGraphSpace O →L[ℝ] EnergyGraphSpace O →L[ℝ] ℝ) :=
  @ContinuousLinearMap.hasOpNorm ℝ ℝ (EnergyGraphSpace O)
    (EnergyGraphSpace O →L[ℝ] ℝ) inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance (RingHom.id ℝ)

/-- Uniform operator norm bound for the actual continuous bilinear form. -/
theorem energyForm_norm_le {O : Set (Space n)} {a : Point n → Mat n}
    {b : Point n → Yau.RIdx n → ℝ} {t A D : ℝ}
    (h : EnergySliceBounds O a b t A D) : ‖energyForm h‖ ≤ energyFormBound n A D := by
  apply @ContinuousLinearMap.opNorm_le_bound ℝ ℝ (EnergyGraphSpace O)
    (EnergyGraphSpace O →L[ℝ] ℝ) inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance (RingHom.id ℝ) (energyForm h) (energyFormBound n A D)
    (energyFormBound_pos h.1 h.2.1).le
  intro v
  apply (energyForm h v).opNorm_le_bound (mul_nonneg (energyFormBound_pos h.1 h.2.1).le (norm_nonneg _))
  intro w
  exact energyForm_apply_bound h v w

private theorem energy_drift_young {ι : Type*} [Fintype ι] (c g : ι → ℝ)
    (u D lam : ℝ) (hlam : 0 < lam) (hC : (∑ j, |c j|^2) ≤ D^2) :
    2 * (∑ j, c j * g j * u) ≤ lam * (∑ j, (g j)^2) + (D^2 / lam) * u^2 := by
  have hs : 0 ≤ ∑ j, (lam * g j - c j * u)^2 :=
    Finset.sum_nonneg fun j _ => sq_nonneg _
  have hid : (∑ j, (lam * g j - c j * u)^2) =
      lam^2 * (∑ j, (g j)^2) - 2*lam*(∑ j, c j*g j*u) + (∑ j, (c j)^2)*u^2 := by
    calc
      _ = ∑ j, (lam^2 * (g j)^2 - 2*lam*(c j*g j*u) + (c j)^2*u^2) := by
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = _ := by simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
        Finset.mul_sum, Finset.sum_mul]
  rw [hid] at hs
  have hc : (∑ j, (c j)^2) ≤ D^2 := by simpa only [sq_abs] using hC
  have hmul := mul_le_mul_of_nonneg_right hc (sq_nonneg u)
  have hdiv : lam * (D^2 / lam) = D^2 := mul_div_cancel₀ _ hlam.ne'
  apply (mul_le_mul_iff_right₀ hlam).mp
  nlinarith [sq_nonneg (lam * (∑ j, c j*g j*u))]

private theorem energyLp_square_integrable {α : Type*} [MeasurableSpace α]
    {μ : Measure α} (u : Lp ℝ 2 μ) : Integrable (fun x => (u x)^2) μ := by
  have hh : Integrable (fun x => u x * u x) μ :=
    (Lp.memLp u).integrable_mul (Lp.memLp u)
  simpa only [pow_two] using hh

private theorem energyLp_norm_sq_integral {α : Type*} [MeasurableSpace α]
    {μ : Measure α} (u : Lp ℝ 2 μ) : ‖u‖^2 = ∫ x, (u x)^2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by simp only [RCLike.inner_apply, conj_trivial, pow_two]

/-- The sharp drift-square Gårding inequality for actual elliptic coefficients.
This uses no Poincaré inequality and imposes no connectedness assumption. -/
theorem energyForm_garding {O : Set (Space n)} {Q : Set (Point n)}
    {a : Point n → Mat n} {b : Point n → Yau.RIdx n → ℝ} {t A D lam upper : ℝ}
    (h : EnergySliceBounds O a b t A D) (hO : MeasurableSet O)
    (hEll : Elliptic Q a lam upper) (hSlice : ∀ x ∈ O, (x,t) ∈ Q)
    (v : EnergyGraphSpace O) :
    lam * (∑ i, ‖energyGradientProjection O i v‖^2) -
      (D^2 / lam) * ‖energyValueProjection O v‖^2 ≤ 2 * energyFormValue O a b t v v := by
  have hG : Integrable (fun x => ∑ i, (energyGradientProjection O i v x)^2) (volume.restrict O) :=
    integrable_finsetSum _ fun i _ => energyLp_square_integrable _
  have hu := energyLp_square_integrable (energyValueProjection O v)
  have hPoint : ∀ᵐ x ∂volume.restrict O,
      lam * (∑ i, (energyGradientProjection O i v x)^2) -
        (D^2 / lam) * (energyValueProjection O v x)^2 ≤
      2 * ((∑ i, ∑ j, a (x,t) i j * energyGradientProjection O j v x *
        energyGradientProjection O i v x) -
        ∑ j, energyDrift a b (x,t) j * energyGradientProjection O j v x *
          energyValueProjection O v x) := by
    filter_upwards [ae_restrict_mem hO, h.2.2.2.2.2] with x hx hcx
    have hPrincipal := ((hEll.2.2 (x,t) (hSlice x hx)).2
      (fun i => energyGradientProjection O i v x)).1
    have hPrincipalEq : (∑ i, ∑ j, a (x,t) i j * energyGradientProjection O i v x *
        energyGradientProjection O j v x) =
        ∑ i, ∑ j, a (x,t) i j * energyGradientProjection O j v x *
          energyGradientProjection O i v x := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hPrincipalEq] at hPrincipal
    have hYoung := energy_drift_young (fun j => energyDrift a b (x,t) j)
      (fun j => energyGradientProjection O j v x) (energyValueProjection O v x)
      D lam hEll.1 hcx
    linarith
  have hInt := integral_mono_ae ((hG.const_mul lam).sub (hu.const_mul (D^2 / lam)))
    ((energyForm_integrable h v v).const_mul 2) hPoint
  simp only [Pi.sub_apply] at hInt
  rw [integral_sub (hG.const_mul lam) (hu.const_mul (D^2 / lam)),
    integral_const_mul, integral_const_mul, integral_const_mul,
    integral_finsetSum _ fun i _ => energyLp_square_integrable _] at hInt
  simp_rw [← energyLp_norm_sq_integral] at hInt
  exact hInt

/-- The identical estimate for the bundled form. -/
theorem energyForm_garding_clm {O : Set (Space n)} {Q : Set (Point n)}
    {a : Point n → Mat n} {b : Point n → Yau.RIdx n → ℝ} {t A D lam upper : ℝ}
    (h : EnergySliceBounds O a b t A D) (hO : MeasurableSet O)
    (hEll : Elliptic Q a lam upper) (hSlice : ∀ x ∈ O, (x,t) ∈ Q)
    (v : EnergyGraphSpace O) :
    lam * (∑ i, ‖energyGradientProjection O i v‖^2) -
      (D^2 / lam) * ‖energyValueProjection O v‖^2 ≤ 2 * energyForm h v v := by
  rw [energyForm_apply]
  exact energyForm_garding h hO hEll hSlice v

end Yau.LeafProofs.L16Aux
