import Yau.Proofs.HeatSmoothExhaustionParameters
import Yau.Proofs.HeatSmoothExhaustionBumps

noncomputable section
open Set Filter
open scoped Topology ContDiff

namespace Yau.Proofs.SmoothExhaustionAux
open Yau

theorem affinePerturbation_bound {α E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {N : ℕ} (f : α → ℝ) (v : Fin N → α → E) (w : Fin N → α → ℝ)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ i p, ‖v i p‖+|w i p| ≤ C)
    (θ : Fin N → AffineBlock E) (p : α) :
    |affinePerturbation f v w θ p-f p| ≤ (N : ℝ)*C*‖θ‖ := by
  classical
  rw [affinePerturbation,add_sub_cancel_left]
  calc
    _ ≤ ∑ i, |(θ i).1 (v i p)+(θ i).2*w i p| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin N, ‖θ‖*C := by
      apply Finset.sum_le_sum
      intro i _
      have ha : ‖(θ i).1‖ ≤ ‖θ‖ := (norm_fst_le (θ i)).trans (norm_le_pi_norm θ i)
      have hb : |(θ i).2| ≤ ‖θ‖ := by
        simpa only [Real.norm_eq_abs] using (norm_snd_le (θ i)).trans (norm_le_pi_norm θ i)
      have Hop : |(θ i).1 (v i p)| ≤ ‖(θ i).1‖*‖v i p‖ := by
        simpa only [Real.norm_eq_abs] using (θ i).1.le_opNorm (v i p)
      have Hterm := abs_add_le ((θ i).1 (v i p)) ((θ i).2*w i p)
      rw [abs_mul] at Hterm
      have HA := mul_le_mul_of_nonneg_right ha (norm_nonneg (v i p))
      have HB := mul_le_mul_of_nonneg_right hb (abs_nonneg (w i p))
      have HC := mul_le_mul_of_nonneg_left (hbound i p) (norm_nonneg θ)
      nlinarith
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul];ring

theorem affinePerturbation_smoothFn {n N : ℕ} {M : ComplexManifold n}
    (f : M.Carrier → ℝ) (v : Fin N → M.Carrier → ComplexVector n)
    (w : Fin N → M.Carrier → ℝ) (hf : SmoothFn f)
    (hv : ∀ i a, ContDiffOn ℝ ∞ (fun z => v i (chartInv a z)) (chartTarget a))
    (hw : ∀ i, SmoothFn (w i)) (θ : Fin N → AffineBlock (ComplexVector n)) :
    SmoothFn (affinePerturbation f v w θ) := by
  intro a
  apply (hf a).add
  apply ContDiffOn.sum
  intro i _
  exact (contDiffOn_const.clm_apply (hv i a)).add (contDiffOn_const.mul (hw i a))

def ChartRegularZero {n : ℕ} {M : ComplexManifold n} (f : M.Carrier → ℝ) : Prop :=
  ∀ p, f p=0 → ∃ a : M.Carrier,
    p ∈ (chartAt (ComplexVector n) a).source ∧
      fderiv ℝ (inChart a f) (chartPt a p) ≠ 0

theorem exists_small_regular_perturbation {n : ℕ} {M : ComplexManifold n}
    (f : M.Carrier → ℝ) (hf : SmoothFn f)
    (S : Set M.Carrier) (hS : IsCompact S) :
    ∃ g : M.Carrier → ℝ, SmoothFn g ∧ (∀ p, |g p-f p| < 1/4) ∧
      ∀ p ∈ S, g p=0 → ∃ a : M.Carrier,
        p ∈ (chartAt (ComplexVector n) a).source ∧
        fderiv ℝ (inChart a g) (chartPt a p) ≠ 0 := by
  classical
  obtain ⟨N,a,V,v,w,C,hC,hV,hcover,hidentity,hv,hw,hbound⟩ := finite_affine_bump_family hS
  let E := ComplexVector n
  let A := fun i : Fin N => E × OtherParameters (E := E) i
  let U := fun i : Fin N => chartTarget (a i) ×ˢ (univ : Set (OtherParameters (E := E) i))
  let G := fun i : Fin N => badParameterGraph
    (inChart (a i) f) (fun j z => v j (chartInv (a i) z))
    (fun j z => w j (chartInv (a i) z)) i
  have hG (i : Fin N) : DifferentiableOn ℝ (G i) (U i) :=
    (badParameterGraph_smooth _ _ _ (isOpen_extChartAt_target (I := ComplexModel n) (a i))
      (hf (a i)) (fun j => hv j (a i)) (fun j => hw j (a i)) i).differentiableOn (by simp)
  let ε := 1/(4*(1+(N : ℝ)*C))
  have hNC : 0 ≤ (N : ℝ)*C := mul_nonneg (Nat.cast_nonneg N) hC.le
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨θ,hθ,havoid⟩ := exists_small_avoiding_finite_images A U G hG
    (fun i => affine_graph_parameter_dimension (E := E) i) hε
  let g := affinePerturbation f v w θ
  have hsmall (p : M.Carrier) : |g p-f p| < 1/4 := by
    have H := affinePerturbation_bound f v w C hC.le hbound θ p
    have Hθ := (lt_div_iff₀ (show 0 < 4*(1+(N : ℝ)*C) by positivity)).mp hθ
    change |g p-f p| ≤ (N : ℝ)*C*‖θ‖ at H
    nlinarith [norm_nonneg θ]
  refine ⟨g,affinePerturbation_smoothFn f v w hf hv hw θ,hsmall,?_⟩
  intro p hp hpzero
  obtain ⟨i,hpi⟩ := mem_iUnion.mp (hcover hp)
  obtain ⟨z,hz,hzp⟩ := hpi
  have hza := (hV i).2 hz
  have hsrc : p ∈ (chartAt (ComplexVector n) (a i)).source := by
    rw [← hzp]
    simpa only [extChartAt_source,chartInv] using (extChartAt (ComplexModel n) (a i)).map_target hza
  have hpt : chartPt (a i) p=z := by rw [← hzp];exact (extChartAt (ComplexModel n) (a i)).right_inv hza
  refine ⟨a i,hsrc,?_⟩
  rw [hpt]
  intro hsing
  apply havoid i
  apply singular_zero_mem_graph (inChart (a i) f)
    (fun j z => v j (chartInv (a i) z)) (fun j z => w j (chartInv (a i) z))
    (isOpen_extChartAt_target (I := ComplexModel n) (a i)) (hV i).1 (hV i).2
    (hf (a i)) (fun j => hv j (a i)) (fun j => hw j (a i)) i (hidentity i) θ z hz
  · change g (chartInv (a i) z)=0
    rwa [hzp]
  · exact hsing

end Yau.Proofs.SmoothExhaustionAux
