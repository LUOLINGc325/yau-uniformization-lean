import Yau.LeafProofs.L16CompatibleActualResidual
import Yau.LeafProofs.L16CompatibleParametrixFactory
import Yau.LeafProofs.L16HalfSpaceHeatSolver

open MeasureTheory Filter Set
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic

local instance finitePhysical_group {n : ℕ} (α : ℝ) (O : Set (Space n)) (T : ℝ) :
    NormedAddCommGroup (compatibleHolderGraph α O T) := inferInstance
local instance finitePhysical_space {n : ℕ} (α : ℝ) (O : Set (Space n)) (T : ℝ) :
    NormedSpace ℝ (compatibleHolderGraph α O T) := inferInstance

theorem schauderBound_finset_sum {n : ℕ} {ι : Type*} (s : Finset ι)
    {α : ℝ} {Q : Set (Point n)} {u : ι → Point n → ℝ} {C : ι → ℝ}
    (hu : ∀ i ∈ s, SchauderBound α Q (u i) (C i)) :
    SchauderBound α Q (fun p => ∑ i ∈ s, u i p) (∑ i ∈ s, C i) := by
  classical
  revert hu
  induction s using Finset.induction_on with
  | empty => intro hu; simpa only [Finset.sum_empty] using schauderBound_zero (n := n) α Q
  | @insert i s hi ih =>
    intro hu
    simpa only [Finset.sum_insert hi] using
      schauderBound_add (hu i (Finset.mem_insert_self i s))
        (ih (fun j hj => hu j (Finset.mem_insert_of_mem hj)))

/-- Finite sums keep a lower-jet budget independent of their higher-jet
Schauder budget. The derivative in the output is the actual derivative. -/
theorem lowPair_holderBound_finset_sum {n : ℕ} {ι : Type*} (s : Finset ι)
    {α : ℝ} {Q : Set (Point n)} {u : ι → Point n → ℝ} {L : ι → ℝ}
    (hu : ∀ i ∈ s, C2 Q (u i))
    (hLow : ∀ i ∈ s, HolderBound α Q (fun p => (u i p,spatialD (u i) p)) (L i)) :
    HolderBound α Q (fun p => (∑ i ∈ s, u i p,spatialD (fun q => ∑ i ∈ s, u i q) p))
      (∑ i ∈ s, L i) := by
  have hD (p : Point n) (hp : p ∈ Q) : spatialD (fun q => ∑ i ∈ s, u i q) p =
      ∑ i ∈ s, spatialD (u i) p := by
    exact fderiv_fun_sum (fun i hi => ((hu i hi).2.2.2.2.1 p hp).differentiableAt (by norm_num))
  apply holderBound_congr_on (holderBound_finset_sum s hLow)
  intro p hp
  apply Prod.ext
  · simp only [Prod.fst_sum]
  · simpa only [Prod.snd_sum] using (hD p hp).symm

/-- The actual finite physical sum. Each summand has already been pulled
back and cut off in its own genuine chart or interior ball. -/
def finitePhysicalParametrix {n : ℕ} {ι : Type*} {α T : ℝ} {O : Set (Space n)}
    (s : Finset ι) (W : ι → compatibleHolderGraph α O T → Point n → ℝ)
    (f : compatibleHolderGraph α O T) (p : Point n) : ℝ := ∑ i ∈ s, W i f p

theorem finitePhysicalParametrix_add {n : ℕ} {ι : Type*} {α T : ℝ} {O : Set (Space n)}
    (s : Finset ι) (W : ι → compatibleHolderGraph α O T → Point n → ℝ)
    (hAdd : ∀ i ∈ s, ∀ f g p, p ∈ cylinder univ 0 T → W i (f+g) p = W i f p+W i g p)
    (f g : compatibleHolderGraph α O T) {p : Point n} (hp : p ∈ cylinder univ 0 T) :
    finitePhysicalParametrix s W (f+g) p = finitePhysicalParametrix s W f p+finitePhysicalParametrix s W g p := by
  classical
  change (∑ i ∈ s, W i (f+g) p) = _
  calc
    _ = ∑ i ∈ s, (W i f p+W i g p) := Finset.sum_congr rfl (fun i hi => hAdd i hi f g p hp)
    _ = _ := Finset.sum_add_distrib

theorem finitePhysicalParametrix_smul {n : ℕ} {ι : Type*} {α T : ℝ} {O : Set (Space n)}
    (s : Finset ι) (W : ι → compatibleHolderGraph α O T → Point n → ℝ)
    (hSmul : ∀ i ∈ s, ∀ (c : ℝ) f p, p ∈ cylinder univ 0 T → W i (c • f) p = c*W i f p)
    (c : ℝ) (f : compatibleHolderGraph α O T) {p : Point n} (hp : p ∈ cylinder univ 0 T) :
    finitePhysicalParametrix s W (c • f) p = c*finitePhysicalParametrix s W f p := by
  classical
  change (∑ i ∈ s, W i (c • f) p) = _
  calc
    _ = ∑ i ∈ s, c*W i f p := Finset.sum_congr rfl (fun i hi => hSmul i hi c f p hp)
    _ = _ := (Finset.mul_sum ..).symm

/-- Actual finite patch equations, a true physical partition and actual
commutator estimates assemble into the literal original-operator residual.
No existence theorem or unproved residual estimate is used in this algebra. -/
theorem finitePhysicalParametrix_data {n : ℕ} {ι : Type*} {α T κ : ℝ} {O : Set (Space n)}
    (hT : 0 ≤ T) (s : Finset ι) (a : Point n → Mat n) (b : Point n → Yau.RIdx n → ℝ)
    (ψ : ι → Space n → ℝ) (C E : ι → ℝ)
    (W H : ι → compatibleHolderGraph α O T → Point n → ℝ)
    (hPartition : ∀ x ∈ closure O, (∑ i ∈ s, ψ i x) = 1)
    (hW : ∀ i ∈ s, ∀ f,
      SchauderBound α (cylinder univ 0 T) (W i f) (C i*‖f‖) ∧
      HolderBound α (cylinder univ 0 T) (fun p => (W i f p,spatialD (W i f) p)) (C i*‖f‖*κ) ∧
      (∀ x, W i f (x,0) = 0) ∧
      (∀ x ∈ frontier O, ∀ t ∈ Icc 0 T, W i f (x,t) = 0) ∧
      ∀ p ∈ cylinder (closure O) 0 T,
        linearOp (cylinder (closure O) 0 T) a b (W i f) p = ψ i p.1*compatibleHolderFun f p-H i f p)
    (hError : ∀ i ∈ s, ∀ f,
      HolderBound α (cylinder (closure O) 0 T) (H i f) (E i*‖f‖*κ) ∧
      ∀ x ∈ frontier O, H i f (x,0) = 0) :
    ∀ f,
      SchauderBound α (cylinder univ 0 T) (finitePhysicalParametrix s W f) ((∑ i ∈ s, C i)*‖f‖) ∧
      HolderBound α (cylinder univ 0 T)
        (fun p => (finitePhysicalParametrix s W f p,spatialD (finitePhysicalParametrix s W f) p))
        ((∑ i ∈ s, C i)*‖f‖*κ) ∧
      (∀ x, finitePhysicalParametrix s W f (x,0) = 0) ∧
      (∀ x ∈ frontier O, ∀ t ∈ Icc 0 T, finitePhysicalParametrix s W f (x,t) = 0) ∧
      HolderBound α (cylinder (closure O) 0 T)
        (compatibleActualResidual O a b (finitePhysicalParametrix s W) f)
        ((∑ i ∈ s, E i)*‖f‖*κ) ∧
      (∀ x ∈ frontier O, compatibleActualResidual O a b (finitePhysicalParametrix s W) f (x,0) = 0) ∧
      ∀ p ∈ cylinder (closure O) 0 T,
        linearOp (cylinder (closure O) 0 T) a b (finitePhysicalParametrix s W f) p =
          compatibleHolderFun f p-∑ i ∈ s, H i f p := by
  classical
  intro f
  have hSch := schauderBound_finset_sum s (fun i hi => (hW i hi f).1)
  have hLow := lowPair_holderBound_finset_sum s (fun i hi => (hW i hi f).1.1)
    (fun i hi => (hW i hi f).2.1)
  have hInitial (x : Space n) : finitePhysicalParametrix s W f (x,0) = 0 :=
    Finset.sum_eq_zero (fun i hi => (hW i hi f).2.2.1 x)
  have hLateral (x : Space n) (hx : x ∈ frontier O) (t : ℝ) (ht : t ∈ Icc 0 T) :
      finitePhysicalParametrix s W f (x,t) = 0 :=
    Finset.sum_eq_zero (fun i hi => (hW i hi f).2.2.2.1 x hx t ht)
  have hOperator (p : Point n) (hp : p ∈ cylinder (closure O) 0 T) :
      linearOp (cylinder (closure O) 0 T) a b (finitePhysicalParametrix s W f) p =
        compatibleHolderFun f p-∑ i ∈ s, H i f p := by
    change linearOp (cylinder (closure O) 0 T) a b (fun q => ∑ i ∈ s, W i f q) p = _
    rw [linearOp_sum s
      (fun i hi => c2_cylinder_restrict_space (hW i hi f).1.1) hp]
    calc
      _ = ∑ i ∈ s, (ψ i p.1*compatibleHolderFun f p-H i f p) :=
        Finset.sum_congr rfl (fun i hi => (hW i hi f).2.2.2.2 p hp)
      _ = _ := by
        rw [Finset.sum_sub_distrib,← Finset.sum_mul,hPartition p.1 hp.1,one_mul]
  have hResidual (p : Point n) (hp : p ∈ cylinder (closure O) 0 T) :
      compatibleActualResidual O a b (finitePhysicalParametrix s W) f p = -(∑ i ∈ s, H i f p) := by
    rw [compatibleActualResidual,hOperator p hp]
    ring
  have hErrorSum := holderBound_finset_sum s (fun i hi => (hError i hi f).1)
  have hNeg := holderBound_neg hErrorSum
  have hResidualBound := holderBound_congr_on hNeg (fun p hp => (hResidual p hp).symm)
  refine ⟨?_,?_,hInitial,hLateral,?_,?_,hOperator⟩
  · change SchauderBound α (cylinder univ 0 T) (fun p => ∑ i ∈ s, W i f p) _
    simpa only [← Finset.sum_mul] using hSch
  · change HolderBound α (cylinder univ 0 T)
      (fun p => (∑ i ∈ s, W i f p,spatialD (fun q => ∑ i ∈ s, W i f q) p)) _
    simpa only [← Finset.sum_mul] using hLow
  · simpa only [← Finset.sum_mul] using hResidualBound
  · intro x hx
    have hZero : (∑ i ∈ s, H i f (x,0)) = 0 := Finset.sum_eq_zero (fun i hi => (hError i hi f).2 x hx)
    rw [hResidual (x,0) ⟨hx.1,le_rfl,hT⟩,hZero,neg_zero]

/-- Once the actual finite commutator budget is small, the actual finite
physical parametrix gives a genuine compatible inverse. Every analytic input
here is a statement about the actual patches, not an abstract operator bound. -/
theorem finitePhysicalParametrix_compatible_inverse {n : ℕ} {ι : Type*} {α T κ : ℝ} {O : Set (Space n)}
    (hα : 0 < α) (hT : 0 ≤ T) (_hκ : 0 ≤ κ) (hκ1 : κ ≤ 1)
    (s : Finset ι) (a : Point n → Mat n) (b : Point n → Yau.RIdx n → ℝ)
    (ψ : ι → Space n → ℝ) (C E : ι → ℝ)
    (W H : ι → compatibleHolderGraph α O T → Point n → ℝ)
    (hC : ∀ i ∈ s, 0 ≤ C i)
    (hSmall : (∑ i ∈ s, E i)*κ ≤ (1/4 : ℝ))
    (hPartition : ∀ x ∈ closure O, (∑ i ∈ s, ψ i x) = 1)
    (hWAdd : ∀ i ∈ s, ∀ f g p, p ∈ cylinder univ 0 T → W i (f+g) p = W i f p+W i g p)
    (hWSmul : ∀ i ∈ s, ∀ (c : ℝ) f p, p ∈ cylinder univ 0 T → W i (c • f) p = c*W i f p)
    (hW : ∀ i ∈ s, ∀ f,
      SchauderBound α (cylinder univ 0 T) (W i f) (C i*‖f‖) ∧
      HolderBound α (cylinder univ 0 T) (fun p => (W i f p,spatialD (W i f) p)) (C i*‖f‖*κ) ∧
      (∀ x, W i f (x,0) = 0) ∧
      (∀ x ∈ frontier O, ∀ t ∈ Icc 0 T, W i f (x,t) = 0) ∧
      ∀ p ∈ cylinder (closure O) 0 T,
        linearOp (cylinder (closure O) 0 T) a b (W i f) p = ψ i p.1*compatibleHolderFun f p-H i f p)
    (hError : ∀ i ∈ s, ∀ f,
      HolderBound α (cylinder (closure O) 0 T) (H i f) (E i*‖f‖*κ) ∧
      ∀ x ∈ frontier O, H i f (x,0) = 0) :
    ∃ U : compatibleHolderGraph α O T → Point n → ℝ,
      (∀ f g p, p ∈ cylinder univ 0 T → U (f+g) p = U f p+U g p) ∧
      (∀ (c : ℝ) f p, p ∈ cylinder univ 0 T → U (c • f) p = c*U f p) ∧
      ∀ f,
        SchauderBound α (cylinder univ 0 T) (U f) ((4*(1+∑ i ∈ s, C i))*‖f‖) ∧
        HolderBound α (cylinder univ 0 T) (fun p => (U f p,spatialD (U f) p))
          ((4*(1+∑ i ∈ s, C i))*‖f‖) ∧
        (∀ x, U f (x,0) = 0) ∧
        (∀ x ∈ frontier O, ∀ t ∈ Icc 0 T, U f (x,t) = 0) ∧
        ∀ p ∈ cylinder (closure O) 0 T,
          linearOp (cylinder (closure O) 0 T) a b (U f) p = compatibleHolderFun f p := by
  let P := finitePhysicalParametrix s W
  let D := compatibleActualResidual O a b P
  let CP : ℝ := 1+∑ i ∈ s, C i
  have hSumC : 0 ≤ ∑ i ∈ s, C i := Finset.sum_nonneg hC
  have hCP : 0 < CP := by dsimp only [CP]; linarith only [hSumC]
  have hData := finitePhysicalParametrix_data hT s a b ψ C E W H hPartition hW hError
  have hPC2 f : C2 (cylinder univ 0 T) (P f) := (hData f).1.1
  have hP f : SchauderBound α (cylinder univ 0 T) (P f) (CP*‖f‖) ∧
      HolderBound α (cylinder univ 0 T) (fun p => (P f p,spatialD (P f) p)) (CP*‖f‖) := by
    obtain ⟨hSch,hLow,_⟩ := hData f
    have hHigh : (∑ i ∈ s, C i)*‖f‖ ≤ CP*‖f‖ := by dsimp only [CP]; nlinarith only [norm_nonneg f]
    have hLowCost : (∑ i ∈ s, C i)*‖f‖*κ ≤ CP*‖f‖ :=
      (mul_le_of_le_one_right (mul_nonneg hSumC (norm_nonneg f)) hκ1).trans hHigh
    exact ⟨schauderBound_mono_const hSch hHigh,holderBound_mono_const hLow hLowCost⟩
  have hAdd (f g) (p : Point n) (hp : p ∈ cylinder univ 0 T) :
      P (f+g) p = P f p+P g p := finitePhysicalParametrix_add s W hWAdd f g hp
  have hSmul (c : ℝ) (f) (p : Point n) (hp : p ∈ cylinder univ 0 T) :
      P (c • f) p = c*P f p := finitePhysicalParametrix_smul s W hWSmul c f hp
  have hOperator f p (_hp : p ∈ cylinder (closure O) 0 T) :
      linearOp (cylinder (closure O) 0 T) a b (P f) p = compatibleHolderFun f p+D f p := by
    dsimp only [D,compatibleActualResidual]
    ring
  have hRefined f : HolderBound α (cylinder (closure O) 0 T) (D f)
      (‖f‖/4+1*‖f.val.val.1‖/4) ∧ ∀ p ∈ cylinder (closure O) 0 T, |D f p| ≤ ‖f‖/(4*1) := by
    have hBound := (hData f).2.2.2.2.1
    have hBudget : (∑ i ∈ s, E i)*‖f‖*κ ≤ ‖f‖/4 := by
      have h := mul_le_mul_of_nonneg_right hSmall (norm_nonneg f)
      nlinarith only [h]
    refine ⟨holderBound_mono_const hBound (by nlinarith only [hBudget,norm_nonneg f.val.val.1]),?_⟩
    intro p hp
    have h := (hBound.2.1 p hp).trans hBudget
    simpa only [Real.norm_eq_abs,mul_one] using h
  have hResult := compatibleParametrix_linear_inverse hα hT (by norm_num : (0 : ℝ) < 1)
    hCP a b P D hP (fun f => (hData f).2.2.1) (fun f => (hData f).2.2.2.1)
    hAdd hSmul hOperator
    (fun f g p hp => compatibleActualResidual_add a b P hPC2 hAdd f g hp)
    (fun c f p hp => compatibleActualResidual_smul a b P hPC2 hSmul c f hp)
    (fun f => (hData f).2.2.2.2.2.1) hRefined
  simpa only [CP,show (2 : ℝ)*(1+1) = 4 by norm_num] using hResult

end Yau.LeafProofs.L16Aux
