import Yau.Proofs.P06SmallTimeCylinderWordEnergy

/-! Ordered Leibniz expansion combines the actual cutoff derivative budget
with finite spatial energy. No cutoff-dependent constant is chosen after τ. -/
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Filter
open scoped Topology ContDiff

namespace Yau.NodeProofs.P06Aux.SmallTimeCylinder
open Yau.Parabolic Yau.LeafProofs.L16Aux CylinderReg

theorem div_pow_mono {τ C : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hC : 0 ≤ C)
    {i j : ℕ} (hij : i ≤ j) : C / τ ^ i ≤ C / τ ^ j :=
  div_le_div_of_nonneg_left hC (pow_pos hτ _) (pow_le_pow_of_le_one hτ.le hτ1 hij)

theorem square_div_mul_div (A B τ : ℝ) (hτ : τ ≠ 0) (i j : ℕ) :
    (A / τ ^ i) ^ 2 * (B / τ ^ j) = A ^ 2 * B / τ ^ (2 * i + j) := by
  rw [show 2 * i + j = i * 2 + j by omega, pow_add, pow_mul]
  field_simp [hτ]
  <;> ring

theorem square_mul_integral_le {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {K : Set X} (hK : MeasurableSet K) (f g : X → ℝ)
    (hInt : Integrable (fun p => (f p * g p) ^ 2) μ)
    (hg : IntegrableOn (fun p => (g p) ^ 2) K μ)
    (hzero : ∀ p ∉ K, f p = 0) (B : ℝ) (hB : 0 ≤ B)
    (hBound : ∀ p ∈ K, |f p| ≤ B) :
    (∫ p, (f p * g p) ^ 2 ∂μ) ≤ B ^ 2 * ∫ p in K, (g p) ^ 2 ∂μ := by
  have hEq : (∫ p in K, (f p * g p) ^ 2 ∂μ) = ∫ p, (f p * g p) ^ 2 ∂μ :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun p hp => by rw [hzero p hp]; simp)
  rw [← hEq, ← integral_const_mul]
  apply setIntegral_mono_on hInt.integrableOn (hg.const_mul (B ^ 2)) hK
  intro p hp
  have hf : (f p) ^ 2 ≤ B ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hBound p hp) 2
  rw [mul_pow]
  exact mul_le_mul_of_nonneg_right hf (sq_nonneg _)

variable {n : ℕ} {α : Type} [Fintype α] [DecidableEq α]

theorem exists_small_time_cutoff_word_energy_constant
    (q : Yau.RIdx n → Yau.RIdx n → Point n → ℝ)
    (e1 : α → α → Yau.RIdx n → Point n → ℝ) (e0 : α → α → Point n → ℝ)
    (hq : ∀ i j, ContDiff ℝ ∞ (q i j)) (hcq : ∀ i j, HasCompactSupport (q i j))
    (he1 : ∀ r c i, ContDiff ℝ ∞ (e1 r c i)) (hce1 : ∀ r c i, HasCompactSupport (e1 r c i))
    (he0 : ∀ r c, ContDiff ℝ ∞ (e0 r c)) (hce0 : ∀ r c, HasCompactSupport (e0 r c))
    {Q : Set (Point n)} (hQ : IsOpen Q) (χ : Point n → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ) (hχQ : tsupport χ ⊆ Q)
    (lam upper A : ℝ) (hlam : 0 < lam) (hA : 0 ≤ A)
    (hEll : ∀ (τ : ℝ) (hτ : 0 < τ), τ ≤ 1 →
      Elliptic (timeScale τ hτ.ne' '' Q) (heatPrincipal q) lam upper)
    (ha : ∀ (τ : ℝ) (hτ : 0 < τ), τ ≤ 1 →
      ∀ p ∈ timeScale τ hτ.ne' '' Q, ∀ i j, |heatPrincipal q p i j| ≤ A)
    (r : α) (w : List (ParabolicJointIdx n)) (J : ℕ) (hw : w.length ≤ J) :
    ∃ C : ℝ, 0 < C ∧ ∀ (τ : ℝ) (hτ : 0 < τ), τ ≤ 1 →
      ∀ U : Point n → α → ℝ,
      (∀ r, ContDiff ℝ ∞ (fun p => U p r)) →
      heatEquation q e1 e0 (timeScale τ hτ.ne' '' Q) U →
      IntegrableOn (valueSquare U) (timeScale τ hτ.ne' '' Q) →
      (∫ p, (regularityCoefficientWord parabolicJointVec w
        (fun p => rescaleProfile τ hτ.ne' χ p * U p r) p) ^ 2) ≤
        (C / τ ^ (6 * J)) * ∫ p in timeScale τ hτ.ne' '' Q, valueSquare U p := by
  classical
  let Split := List (ParabolicJointIdx n) × List (ParabolicJointIdx n)
  have hCut (st : Split) := exists_rescaleProfile_word_bound hχ hcχ st.1
  choose Cχ hCχ hχBound using hCut
  have hVal (st : Split) := exists_small_time_word_local_energy_constant q e1 e0 hq hcq
    he1 hce1 he0 hce0 hQ hcχ hχQ lam upper A hlam hA hEll ha r st.2
  choose CU hCU hUBound using hVal
  let splits := regularityWordSplits w
  let β := Fin splits.length
  let Cterm : Split → ℝ := fun st => (Cχ st) ^ 2 * CU st + 1
  have hCterm (st : Split) : 0 ≤ Cterm st :=
    add_nonneg (mul_nonneg (sq_nonneg _) (hCU st).le) zero_le_one
  let S : ℝ := ∑ i : β, Cterm (splits.get i)
  have hS : 0 ≤ S := Finset.sum_nonneg (fun i _ => hCterm _)
  refine ⟨1 + (splits.length : ℝ) ^ 2 * S, by positivity, ?_⟩
  intro τ hτ hτ1 U hU hPDE hUI
  let T := timeScale (n := n) τ hτ.ne'
  let χτ := rescaleProfile τ hτ.ne' χ
  have hχτ : ContDiff ℝ ∞ χτ := rescaleProfile_contDiff τ hτ.ne' hχ
  have hcχτ : HasCompactSupport χτ := rescaleProfile_compact τ hτ.ne' hcχ
  have hKτ : IsCompact (T '' tsupport χ) := hcχ.image T.continuous
  let term : β → Point n → ℝ := fun i p =>
    regularityCoefficientWord parabolicJointVec (splits.get i).1 χτ p *
      regularityCoefficientWord parabolicJointVec (splits.get i).2 (fun p => U p r) p
  have hTermInt (i : β) : Integrable (fun p => (term i p) ^ 2) volume := by
    have hF := regularityCoefficientWord_regular parabolicJointVec hχτ hcχτ (splits.get i).1
    have hG := regularityCoefficientWord_contDiff parabolicJointVec (hU r) (splits.get i).2
    exact ((hF.1.mul hG).pow 2).continuous.integrable_of_hasCompactSupport
      (compact_square hF.2.1.mul_right)
  have hNonneg : 0 ≤ ∫ p in T '' Q, valueSquare U p :=
    integral_nonneg (fun p => valueSquare_nonneg U p)
  have hTerm (i : β) : (∫ p, (term i p) ^ 2) ≤
      (S / τ ^ (6 * J)) * ∫ p in T '' Q, valueSquare U p := by
    let st := splits.get i
    have hlen := regularityWordSplits_lengths w st (List.get_mem splits i)
    have hF := regularityCoefficientWord_regular parabolicJointVec hχτ hcχτ st.1
    have hG := regularityCoefficientWord_contDiff parabolicJointVec (hU r) st.2
    have hGI : IntegrableOn
        (fun p => (regularityCoefficientWord parabolicJointVec st.2 (fun p => U p r) p) ^ 2)
        (T '' tsupport χ) := (hG.pow 2).continuous.continuousOn.integrableOn_compact hKτ
    have hSupp : tsupport (regularityCoefficientWord parabolicJointVec st.1 χτ) ⊆
        T '' tsupport χ := by
      simpa only [χτ, rescaleProfile_tsupport] using hF.2.2
    have hProd := square_mul_integral_le volume hKτ.measurableSet
      (regularityCoefficientWord parabolicJointVec st.1 χτ)
      (regularityCoefficientWord parabolicJointVec st.2 (fun p => U p r))
      (hTermInt i) hGI (fun p hp => image_eq_zero_of_notMem_tsupport (fun h => hp (hSupp h)))
      (Cχ st / τ ^ st.1.length) (div_nonneg (hCχ st) (pow_nonneg hτ.le _))
      (fun p _ => hχBound st τ hτ hτ1 p)
    have hCombined := hProd.trans (mul_le_mul_of_nonneg_left
      (hUBound st τ hτ hτ1 U hU hPDE hUI) (sq_nonneg _))
    rw [← mul_assoc, square_div_mul_div _ _ τ hτ.ne'] at hCombined
    have hExponent : 2 * st.1.length + 4 * st.2.length ≤ 6 * J := by omega
    have hC0 : 0 ≤ (Cχ st) ^ 2 * CU st := mul_nonneg (sq_nonneg _) (hCU st).le
    have hCoeff : ((Cχ st) ^ 2 * CU st) / τ ^ (2 * st.1.length + 4 * st.2.length) ≤
        S / τ ^ (6 * J) := by
      apply (div_pow_mono hτ hτ1 hC0 hExponent).trans
      apply div_le_div_of_nonneg_right _ (pow_nonneg hτ.le _)
      have hSingle : Cterm st ≤ S := by
        change Cterm (splits.get i) ≤ ∑ j : β, Cterm (splits.get j)
        exact Finset.single_le_sum (f := fun j : β => Cterm (splits.get j))
          (fun j _ => hCterm _) (Finset.mem_univ i)
      exact (by dsimp only [Cterm]; linarith : (Cχ st) ^ 2 * CU st ≤ Cterm st).trans hSingle
    exact hCombined.trans (mul_le_mul_of_nonneg_right hCoeff hNonneg)
  have hWord := regularityCoefficientWord_regular parabolicJointVec (hχτ.mul (hU r))
    hcχτ.mul_right w
  have hWordInt : Integrable (fun p =>
      (regularityCoefficientWord parabolicJointVec w (fun p => χτ p * U p r) p) ^ 2) volume :=
    (hWord.1.pow 2).continuous.integrable_of_hasCompactSupport (compact_square hWord.2.1)
  have hSumInt : Integrable (fun p => ∑ i : β, (term i p) ^ 2) volume :=
    integrable_finsetSum _ (fun i _ => hTermInt i)
  have hPoint (p : Point n) :
      (regularityCoefficientWord parabolicJointVec w (fun p => χτ p * U p r) p) ^ 2 ≤
        (splits.length : ℝ) * ∑ i : β, (term i p) ^ 2 := by
    rw [word_mul parabolicJointVec hχτ (hU r) w p]
    simpa only [list_sum_map_eq_sum_get, term] using
      list_sum_sq_le splits (fun st =>
        regularityCoefficientWord parabolicJointVec st.1 χτ p *
          regularityCoefficientWord parabolicJointVec st.2 (fun p => U p r) p)
  have hFirst := integral_mono hWordInt (hSumInt.const_mul (splits.length : ℝ)) hPoint
  rw [integral_const_mul, integral_finsetSum Finset.univ (fun i _ => hTermInt i)] at hFirst
  have hSum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hTerm i)
  simp only [Finset.sum_const, Finset.card_univ, β, Fintype.card_fin, nsmul_eq_mul] at hSum
  have hTotal := hFirst.trans (mul_le_mul_of_nonneg_left hSum (Nat.cast_nonneg splits.length))
  calc
    _ ≤ ((splits.length : ℝ) ^ 2 * S / τ ^ (6 * J)) *
        ∫ p in T '' Q, valueSquare U p := by convert hTotal using 1 <;> ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right (by linarith) (pow_nonneg hτ.le _)) hNonneg

end Yau.NodeProofs.P06Aux.SmallTimeCylinder
