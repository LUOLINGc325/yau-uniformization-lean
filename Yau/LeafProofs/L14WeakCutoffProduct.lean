import Yau.LeafProofs.L14Wedge
import Yau.LeafProofs.L14CurlRows

set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped Manifold Topology ContDiff ComplexOrder ENNReal Matrix
open MeasureTheory Bundle Filter Module

namespace Yau.LeafProofs.L14Aux
open BundleDbar

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

/-- The distributional product rule for an arbitrary locally square integrable
one-form. Smooth scalar multiplication needs no global boundedness assumption. -/
theorem weakDbar_one_multiply_real
    (χ : M.Carrier → ℝ) (hχ : SmoothFn χ)
    (U : NQForm E 1) (D : NQForm E 2) (hUD : WeakDbar (r := r) E U D) :
    WeakDbar (r := r) E (multiplyForm E (fun x => (χ x : ℂ)) U)
      (multiplyForm E (fun x => (χ x : ℂ)) D + gradientWedge E χ U) := by
  have hηc (a : M.Carrier) :
      ContinuousOn (inChart a (fun x => (χ x : ℂ))) (localDomain (r := r) E a) :=
    (((hχ a).continuousLinearMap_comp Complex.ofRealCLM).mono Set.inter_subset_left).continuousOn
  refine ⟨locallyL2_multiplyForm E _ hηc U hUD.1,
    locallyL2_add E _ _ (locallyL2_multiplyForm E _ hηc D hUD.2.1)
      (locallyL2_gradientWedge E χ hχ U hUD.1), ?_⟩
  intro a I α ψ hψ hcψ hsψ
  let O := localDomain (r := r) E a
  let η := fun z => Complex.ofReal (inChart a χ z)
  let T := fun z => η z * ψ z
  let P := fun i z => η z * wirtBar ψ z (stdVec i)
  let Q := fun i z => wirtBar η z (stdVec i) * ψ z
  have hO : IsOpen O := localDomain_isOpen E a
  have hη : ContDiffOn ℝ ∞ η O :=
    ((hχ a).continuousLinearMap_comp Complex.ofRealCLM).mono Set.inter_subset_left
  have hsT : tsupport T ⊆ tsupport ψ := tsupport_mul_subset_right
  have hT : ContDiff ℝ ∞ T := contDiff_of_contDiffOn_of_tsupport_subset hO T
    (hη.mul hψ.contDiffOn) (hsT.trans hsψ)
  have hcT : HasCompactSupport T := hcψ.of_isClosed_subset (isClosed_tsupport _) hsT
  have hDψ (i : Fin n) : ContDiff ℝ ∞ (fun z => wirtBar ψ z (stdVec i)) := by
    simpa only [contDiffOn_univ] using
      wirtBar_contDiffOn isOpen_univ _ hψ.contDiffOn (stdVec i)
  have hsDψ (i : Fin n) : tsupport (fun z => wirtBar ψ z (stdVec i)) ⊆ tsupport ψ :=
    closure_minimal (support_wirtBar_subset ψ (stdVec i)) (isClosed_tsupport _)
  have hsP (i : Fin n) : tsupport (P i) ⊆ tsupport ψ :=
    tsupport_mul_subset_right.trans (hsDψ i)
  have hP (i : Fin n) : ContDiff ℝ ∞ (P i) :=
    contDiff_of_contDiffOn_of_tsupport_subset hO (P i)
      (hη.mul (hDψ i).contDiffOn) ((hsP i).trans hsψ)
  have hsQ (i : Fin n) : tsupport (Q i) ⊆ tsupport ψ := tsupport_mul_subset_right
  have hQ (i : Fin n) : ContDiff ℝ ∞ (Q i) :=
    contDiff_of_contDiffOn_of_tsupport_subset hO (Q i)
      ((wirtBar_contDiffOn hO η hη (stdVec i)).mul hψ.contDiffOn) ((hsQ i).trans hsψ)
  have hIntP (i j : Fin n) : Integrable
      (fun z => coefficients (r := r) E U a z (fun _ => j) α * P i z) (lebesgueC n) :=
    locallyL2_test_integrable E U hUD.1 a (fun _ => j) α (P i) (hP i).continuous
      (hcψ.of_isClosed_subset (isClosed_tsupport _) (hsP i)) ((hsP i).trans hsψ)
  have hIntQ (i j : Fin n) : Integrable
      (fun z => coefficients (r := r) E U a z (fun _ => j) α * Q i z) (lebesgueC n) :=
    locallyL2_test_integrable E U hUD.1 a (fun _ => j) α (Q i) (hQ i).continuous
      (hcψ.of_isClosed_subset (isClosed_tsupport _) (hsQ i)) ((hsQ i).trans hsψ)
  have hDiff (i j : Fin n) :
      (∫ z, coefficients (r := r) E U a z (fun _ => j) α *
        wirtBar T z (stdVec i) ∂lebesgueC n) =
      (∫ z, coefficients (r := r) E U a z (fun _ => j) α * Q i z ∂lebesgueC n) +
      (∫ z, coefficients (r := r) E U a z (fun _ => j) α * P i z ∂lebesgueC n) := by
    rw [← integral_add (hIntQ i j) (hIntP i j)]
    apply integral_congr_ae
    apply Eventually.of_forall
    intro z
    by_cases hz : z ∈ tsupport ψ
    · have hdη := (hη.contDiffAt (hO.mem_nhds (hsψ hz))).differentiableAt (by simp)
      dsimp only [T, P, Q]
      rw [wirtBar_mul_rule η ψ z (stdVec i) hdη (hψ.differentiable (by simp) z)]
      ring
    · have hψz : ψ z = 0 := image_eq_zero_of_notMem_tsupport hz
      have hdψ : wirtBar ψ z (stdVec i) = 0 := by
        by_contra hn
        exact hz (support_wirtBar_subset ψ (stdVec i) hn)
      have hdT : wirtBar T z (stdVec i) = 0 := by
        by_contra hn
        exact hz (hsT (support_wirtBar_subset T (stdVec i) hn))
      simp only [P, Q, hψz, hdψ, hdT, mul_zero, zero_add]
  have hcomponent (i j : Fin n) :
      (∫ z, coefficients (r := r) E
        (multiplyForm E (fun x => (χ x : ℂ)) D + gradientWedge E χ U) a z ![i,j] α * ψ z
          ∂lebesgueC n) =
      -(∫ z, coefficients (r := r) E (multiplyForm E (fun x => (χ x : ℂ)) U)
        a z (fun _ => j) α * wirtBar ψ z (stdVec i) ∂lebesgueC n) +
      (∫ z, coefficients (r := r) E (multiplyForm E (fun x => (χ x : ℂ)) U)
        a z (fun _ => i) α * wirtBar ψ z (stdVec j) ∂lebesgueC n) := by
    have hIntD := locallyL2_test_integrable E D hUD.2.1 a ![i,j] α T hT.continuous hcT (hsT.trans hsψ)
    have hleft :
        (∫ z, coefficients (r := r) E
          (multiplyForm E (fun x => (χ x : ℂ)) D + gradientWedge E χ U) a z ![i,j] α * ψ z
            ∂lebesgueC n) =
        (∫ z, coefficients (r := r) E D a z ![i,j] α * T z ∂lebesgueC n) +
        (∫ z, coefficients (r := r) E U a z (fun _ => j) α * Q i z ∂lebesgueC n) -
        (∫ z, coefficients (r := r) E U a z (fun _ => i) α * Q j z ∂lebesgueC n) := by
      calc
        _ = ∫ z, (coefficients (r := r) E D a z ![i,j] α * T z +
            coefficients (r := r) E U a z (fun _ => j) α * Q i z) -
            coefficients (r := r) E U a z (fun _ => i) α * Q j z ∂lebesgueC n := by
          apply integral_congr_ae
          apply Eventually.of_forall
          intro z
          dsimp only []
          by_cases hz : z ∈ O
          · rw [coefficients_add, coefficients_multiplyForm,
              coefficients_gradientWedge_apply E χ hχ U a z hz]
            dsimp only [η, T, Q, inChart]
            ring
          · have hψz : ψ z = 0 := image_eq_zero_of_notMem_tsupport (fun h => hz (hsψ h))
            simp only [T, Q, hψz, mul_zero, add_zero, sub_zero]
        _ = _ := by
          have hsub := integral_sub (hIntD.add (hIntQ i j)) (hIntQ j i)
          simp only [Pi.add_apply] at hsub
          rw [hsub, integral_add hIntD (hIntQ i j)]
    have hright (k l : Fin n) :
        (∫ z, coefficients (r := r) E (multiplyForm E (fun x => (χ x : ℂ)) U)
          a z (fun _ => l) α * wirtBar ψ z (stdVec k) ∂lebesgueC n) =
        ∫ z, coefficients (r := r) E U a z (fun _ => l) α * P k z ∂lebesgueC n := by
      apply integral_congr_ae
      apply Eventually.of_forall
      intro z
      dsimp only []
      rw [coefficients_multiplyForm]
      dsimp only [P, η, inChart]
      ring
    have he := weakDbar_one_component_tests E U D hUD a i j α T hT hcT (hsT.trans hsψ)
    rw [hDiff i j, hDiff j i] at he
    rw [hleft, hright, hright, he]
    ring
  have hI : I = ![I 0,I 1] := by ext k; fin_cases k <;> rfl
  have hdel0 : (fun t : Fin 1 => I ((0 : Fin 2).succAbove t)) = (fun _ => I 1) := by
    ext t; fin_cases t; rfl
  have hdel1 : (fun t : Fin 1 => I ((1 : Fin 2).succAbove t)) = (fun _ => I 0) := by
    ext t; fin_cases t; rfl
  change (∫ z, coefficients (r := r) E
      (multiplyForm E (fun x => (χ x : ℂ)) D + gradientWedge E χ U) a z I α * ψ z ∂lebesgueC n) =
    -∑ k : Fin 2, (-1 : ℂ) ^ k.val * ∫ z,
      coefficients (r := r) E (multiplyForm E (fun x => (χ x : ℂ)) U)
        a z (fun l => I (k.succAbove l)) α * wirtBar ψ z (stdVec (I k)) ∂lebesgueC n
  simpa only [Fin.sum_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one,
    hdel0, hdel1, one_mul, neg_one_mul, neg_add_rev, neg_neg, add_comm, ← hI]
    using hcomponent (I 0) (I 1)

end Yau.LeafProofs.L14Aux
