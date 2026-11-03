import Yau.LeafProofs.L16CoefficientBounds
import Yau.LeafProofs.L16ConstantWrappers

/-! Quantitative Holder bounds for the actual frozen parabolic residuals. -/

open MeasureTheory Filter
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section

namespace Yau.LeafProofs.L16Aux

open Yau.Parabolic Yau.ParabolicCandidates

theorem holderBound_fst {n : ℕ} {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    {α C : ℝ} {Q : Set (Point n)} {g : Point n → E × F} (hg : HolderBound α Q g C) :
    HolderBound α Q (fun p => (g p).1) C := by
  refine ⟨hg.1,?_,?_⟩
  · intro p hp
    exact (le_max_left ‖(g p).1‖ ‖(g p).2‖).trans (hg.2.1 p hp)
  · intro p hp q hq
    have h : ‖(g p).1-(g q).1‖ ≤ ‖g p-g q‖ := le_max_left _ _
    exact h.trans (hg.2.2 p hp q hq)

theorem holderBound_snd {n : ℕ} {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    {α C : ℝ} {Q : Set (Point n)} {g : Point n → E × F} (hg : HolderBound α Q g C) :
    HolderBound α Q (fun p => (g p).2) C := by
  refine ⟨hg.1,?_,?_⟩
  · intro p hp
    exact (le_max_right ‖(g p).1‖ ‖(g p).2‖).trans (hg.2.1 p hp)
  · intro p hp q hq
    have h : ‖(g p).2-(g q).2‖ ≤ ‖g p-g q‖ := le_max_right _ _
    exact h.trans (hg.2.2 p hp q hq)

theorem norm_gradient_component_le {n : ℕ} (G : Space n →L[ℝ] ℝ) (i : Yau.RIdx n) :
    |G (Yau.realVec i)| ≤ ‖G‖ := by
  simpa only [Real.norm_eq_abs,realVec_norm,mul_one] using G.le_opNorm (Yau.realVec i)

theorem norm_hessian_component_le {n : ℕ} (H : Space n →L[ℝ] Space n →L[ℝ] ℝ)
    (i j : Yau.RIdx n) : |H (Yau.realVec i) (Yau.realVec j)| ≤ ‖H‖ := by
  have h := ((H (Yau.realVec i)).le_opNorm (Yau.realVec j)).trans
    (mul_le_mul_of_nonneg_right (H.le_opNorm (Yau.realVec i)) (norm_nonneg _))
  simpa only [Real.norm_eq_abs,realVec_norm,mul_one] using h

theorem holderBound_gradient_component {n : ℕ} {α C : ℝ} {Q : Set (Point n)}
    {G : Point n → Space n →L[ℝ] ℝ} (hG : HolderBound α Q G C) (i : Yau.RIdx n) :
    HolderBound α Q (fun p => G p (Yau.realVec i)) C := by
  refine ⟨hG.1,?_,?_⟩
  · intro p hp
    simpa only [Real.norm_eq_abs] using (norm_gradient_component_le (G p) i).trans (hG.2.1 p hp)
  · intro p hp q hq
    simpa only [Real.norm_eq_abs,sub_apply] using
      (norm_gradient_component_le (G p-G q) i).trans (hG.2.2 p hp q hq)

theorem holderBound_hessian_component {n : ℕ} {α C : ℝ} {Q : Set (Point n)}
    {H : Point n → Space n →L[ℝ] Space n →L[ℝ] ℝ} (hH : HolderBound α Q H C)
    (i j : Yau.RIdx n) :
    HolderBound α Q (fun p => H p (Yau.realVec i) (Yau.realVec j)) C := by
  refine ⟨hH.1,?_,?_⟩
  · intro p hp
    simpa only [Real.norm_eq_abs] using (norm_hessian_component_le (H p) i j).trans (hH.2.1 p hp)
  · intro p hp q hq
    simpa only [Real.norm_eq_abs,sub_apply] using
      (norm_hessian_component_le (H p-H q) i j).trans (hH.2.2 p hp q hq)

theorem holderBound_add {n : ℕ} {V : Type*} [NormedAddCommGroup V]
    {α C D : ℝ} {Q : Set (Point n)} {f g : Point n → V}
    (hf : HolderBound α Q f C) (hg : HolderBound α Q g D) :
    HolderBound α Q (fun p => f p+g p) (C+D) := by
  refine ⟨add_nonneg hf.1 hg.1,fun p hp =>
    (norm_add_le _ _).trans (add_le_add (hf.2.1 p hp) (hg.2.1 p hp)),?_⟩
  intro p hp q hq
  have hEq : (f p+g p)-(f q+g q) = (f p-f q)+(g p-g q) := by abel
  rw [hEq]
  exact ((norm_add_le _ _).trans
    (add_le_add (hf.2.2 p hp q hq) (hg.2.2 p hp q hq))).trans_eq (by ring)

theorem holderBound_neg {n : ℕ} {V : Type*} [NormedAddCommGroup V]
    {α C : ℝ} {Q : Set (Point n)} {f : Point n → V} (hf : HolderBound α Q f C) :
    HolderBound α Q (fun p => -f p) C := by
  refine ⟨hf.1,?_,?_⟩
  · intro p hp
    simpa only [norm_neg] using hf.2.1 p hp
  · intro p hp q hq
    have hEq : -f p-(-f q) = -(f p-f q) := by abel
    rw [hEq,norm_neg]
    exact hf.2.2 p hp q hq

theorem holderBound_sub {n : ℕ} {V : Type*} [NormedAddCommGroup V]
    {α C D : ℝ} {Q : Set (Point n)} {f g : Point n → V}
    (hf : HolderBound α Q f C) (hg : HolderBound α Q g D) :
    HolderBound α Q (fun p => f p-g p) (C+D) := by
  simpa only [sub_eq_add_neg] using holderBound_add hf (holderBound_neg hg)

theorem holderBound_finset_sum {n : ℕ} {ι V : Type*} [NormedAddCommGroup V]
    (s : Finset ι) {α : ℝ} {Q : Set (Point n)} {f : ι → Point n → V} {C : ι → ℝ}
    (hf : ∀ i ∈ s, HolderBound α Q (f i) (C i)) :
    HolderBound α Q (fun p => ∑ i ∈ s, f i p) (∑ i ∈ s, C i) := by
  classical
  revert hf
  induction s using Finset.induction_on with
  | empty => intro hf; simp [HolderBound]
  | @insert i s hi ih =>
    intro hf
    have hS := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
    simpa only [Finset.sum_insert hi] using
      holderBound_add (hf i (Finset.mem_insert_self i s)) hS

/-- The principal residual product retains the small coefficient sup
bound separately from its Holder seminorm. -/
theorem hessian_contraction_holderBound {n : ℕ} {α A B C D : ℝ} {Q : Set (Point n)}
    {q : Yau.RIdx n → Yau.RIdx n → Point n → ℝ}
    {H : Point n → Space n →L[ℝ] Space n →L[ℝ] ℝ}
    (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hq : ∀ i j, HolderBound α Q (q i j) B)
    (hqSup : ∀ i j, ∀ p ∈ Q, |q i j p| ≤ A)
    (hH : HolderBound α Q H C) (hHSup : ∀ p ∈ Q, ‖H p‖ ≤ D) :
    HolderBound α Q
      (fun p => ∑ i : Yau.RIdx n, ∑ j : Yau.RIdx n,
        q i j p*H p (Yau.realVec i) (Yau.realVec j))
      ((Fintype.card (Yau.RIdx n) : ℝ)^2*(A*C+B*D)) := by
  have hEach (i j : Yau.RIdx n) : HolderBound α Q
      (fun p => q i j p*H p (Yau.realVec i) (Yau.realVec j)) (A*C+B*D) := by
    have hSup : ∀ p ∈ Q, ‖H p (Yau.realVec i) (Yau.realVec j)‖ ≤ D := by
      intro p hp
      simpa only [Real.norm_eq_abs] using (norm_hessian_component_le (H p) i j).trans (hHSup p hp)
    simpa only [smul_eq_mul] using holderBound_smul_refined (hq i j)
      (holderBound_hessian_component hH i j) hA hD (hqSup i j) hSup
  have hRow (i : Yau.RIdx n) := holderBound_finset_sum Finset.univ
    (fun j _ => hEach i j)
  have hSum := holderBound_finset_sum Finset.univ (fun i _ => hRow i)
  simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,pow_two,mul_assoc] using hSum

theorem holderBound_const {n : ℕ} {V : Type*} [NormedAddCommGroup V]
    (α : ℝ) (Q : Set (Point n)) (c : V) : HolderBound α Q (fun _ => c) ‖c‖ := by
  refine ⟨norm_nonneg _,fun _ _ => le_rfl,?_⟩
  intro p hp q hq
  simp only [sub_self,norm_zero]
  exact mul_nonneg (norm_nonneg _) (by dsimp only [holderWeight]; positivity)

theorem frozen_patch_coefficient_holderBound {n : ℕ} {α M E : ℝ}
    {Q : Set (Point n)} {a : Point n → Mat n} {φ : Space n → ℝ}
    (ha : HolderBound α Q a M) (hφ : HolderBound α Q (fun p => φ p.1) E)
    (c : Space n) (τ : ℝ) (hFrozen : (c,τ) ∈ Q) (i j : Yau.RIdx n) :
    HolderBound α Q (fun p => φ p.1*(a (c,τ) i j-a p i j)) (4*E*M) := by
  have hConst := holderBound_const α Q (a (c,τ) i j)
  have hEntry := holderBound_matrix_entry ha i j
  have hFrozenNorm : ‖a (c,τ) i j‖ ≤ M := by
    simpa only [Real.norm_eq_abs] using
      (frobenius_entry_abs_le (a (c,τ)) i j).trans (ha.2.1 (c,τ) hFrozen)
  have hDifference := holderBound_mono_const (holderBound_sub hConst hEntry)
    (by linarith : ‖a (c,τ) i j‖+M ≤ 2*M)
  have hProduct := holderBound_mul hφ hDifference
  have hScale : 2*E*(2*M) = 4*E*M := by ring
  simpa only [hScale] using hProduct

def lowerPatchResidual {n : ℕ} (a : Point n → Mat n)
    (b : Point n → Yau.RIdx n → ℝ) (φ : Space n → ℝ) (v : Point n → ℝ)
    (p : Point n) : ℝ :=
  φ p.1*(∑ i, b p i*spatialD v p (Yau.realVec i))+
  (∑ i, ∑ j, a p i j*
    (fderiv ℝ φ p.1 (Yau.realVec i)*spatialD v p (Yau.realVec j)+
      fderiv ℝ φ p.1 (Yau.realVec j)*spatialD v p (Yau.realVec i)+
      v p*fderiv ℝ (fderiv ℝ φ) p.1 (Yau.realVec i) (Yau.realVec j)))+
  v p*(∑ i, b p i*fderiv ℝ φ p.1 (Yau.realVec i))

theorem frozenPatchResidual_eq_principal_sub_lower {n : ℕ} (Q : Set (Point n))
    (a : Point n → Mat n) (b : Point n → Yau.RIdx n → ℝ) (A : Mat n)
    (φ : Space n → ℝ) (v : Point n → ℝ) (p : Point n) :
    frozenPatchResidual Q a b A φ v p =
      (∑ i : Yau.RIdx n, ∑ j : Yau.RIdx n,
        (φ p.1*(A i j-a p i j))*spatialDD v p (Yau.realVec i) (Yau.realVec j))-
        lowerPatchResidual a b φ v p := by
  have hPrincipal : φ p.1*(∑ i : Yau.RIdx n, ∑ j : Yau.RIdx n,
      (A i j-a p i j)*spatialDD v p (Yau.realVec i) (Yau.realVec j)) =
      ∑ i : Yau.RIdx n, ∑ j : Yau.RIdx n,
        (φ p.1*(A i j-a p i j))*spatialDD v p (Yau.realVec i) (Yau.realVec j) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  dsimp only [frozenPatchResidual,lowerPatchResidual]
  rw [hPrincipal]
  ring

theorem lowerPatchResidual_holderBound {n : ℕ} {α M E0 E1 E2 J : ℝ}
    {Q : Set (Point n)} {a : Point n → Mat n} {b : Point n → Yau.RIdx n → ℝ}
    {φ : Space n → ℝ} {v : Point n → ℝ}
    (ha : HolderBound α Q a M) (hb : ∀ i, HolderBound α Q (fun p => b p i) M)
    (hφ : HolderBound α Q (fun p => φ p.1) E0)
    (hφD : ∀ i : Yau.RIdx n,
      HolderBound α Q (fun p => fderiv ℝ φ p.1 (Yau.realVec i)) E1)
    (hφDD : ∀ i j : Yau.RIdx n, HolderBound α Q
      (fun p => fderiv ℝ (fderiv ℝ φ) p.1 (Yau.realVec i) (Yau.realVec j)) E2)
    (hJet : HolderBound α Q (fun p => (v p,spatialD v p)) J) :
    HolderBound α Q (lowerPatchResidual a b φ v)
      ((4*(Fintype.card (Yau.RIdx n) : ℝ)*M*E0+
        8*(Fintype.card (Yau.RIdx n) : ℝ)^2*M*E1+
        4*(Fintype.card (Yau.RIdx n) : ℝ)^2*M*E2+
        4*(Fintype.card (Yau.RIdx n) : ℝ)*M*E1)*J) := by
  have hV := holderBound_fst hJet
  have hDv (i : Yau.RIdx n) := holderBound_gradient_component (holderBound_snd hJet) i
  have hDφ (i : Yau.RIdx n) := hφD i
  have hDDφ (i j : Yau.RIdx n) := hφDD i j
  have hFirstSum := holderBound_finset_sum Finset.univ
    (fun i _ => holderBound_mul (hb i) (hDv i))
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hFirstSum
  have hFirstRaw := holderBound_mul hφ hFirstSum
  have hFirstScale : 2*E0*((Fintype.card (Yau.RIdx n) : ℝ)*(2*M*J)) =
      4*(Fintype.card (Yau.RIdx n) : ℝ)*M*E0*J := by ring
  have hFirst : HolderBound α Q
      (fun p => φ p.1*(∑ i, b p i*spatialD v p (Yau.realVec i)))
      (4*(Fintype.card (Yau.RIdx n) : ℝ)*M*E0*J) := by
    simpa only [hFirstScale] using hFirstRaw
  have hMatrixEach (i j : Yau.RIdx n) : HolderBound α Q
      (fun p => a p i j*
        (fderiv ℝ φ p.1 (Yau.realVec i)*spatialD v p (Yau.realVec j)+
          fderiv ℝ φ p.1 (Yau.realVec j)*spatialD v p (Yau.realVec i)+
          v p*fderiv ℝ (fderiv ℝ φ) p.1 (Yau.realVec i) (Yau.realVec j)))
      (8*M*E1*J+4*M*E2*J) := by
    have hInside := holderBound_add
      (holderBound_add (holderBound_mul (hDφ i) (hDv j)) (holderBound_mul (hDφ j) (hDv i)))
      (holderBound_mul hV (hDDφ i j))
    have hRaw := holderBound_mul (holderBound_matrix_entry ha i j) hInside
    have hScale : 2*M*((2*E1*J+2*E1*J)+2*J*E2) = 8*M*E1*J+4*M*E2*J := by ring
    simpa only [hScale] using hRaw
  have hMatrixRow (i : Yau.RIdx n) := holderBound_finset_sum Finset.univ
    (fun j _ => hMatrixEach i j)
  have hMatrixRaw := holderBound_finset_sum Finset.univ (fun i _ => hMatrixRow i)
  have hMatrix : HolderBound α Q
      (fun p => ∑ i, ∑ j, a p i j*
        (fderiv ℝ φ p.1 (Yau.realVec i)*spatialD v p (Yau.realVec j)+
          fderiv ℝ φ p.1 (Yau.realVec j)*spatialD v p (Yau.realVec i)+
          v p*fderiv ℝ (fderiv ℝ φ) p.1 (Yau.realVec i) (Yau.realVec j)))
      ((Fintype.card (Yau.RIdx n) : ℝ)^2*(8*M*E1*J+4*M*E2*J)) := by
    simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,pow_two,mul_assoc] using hMatrixRaw
  have hLastSum := holderBound_finset_sum Finset.univ
    (fun i _ => holderBound_mul (hb i) (hDφ i))
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hLastSum
  have hLastRaw := holderBound_mul hV hLastSum
  have hLastScale : 2*J*((Fintype.card (Yau.RIdx n) : ℝ)*(2*M*E1)) =
      4*(Fintype.card (Yau.RIdx n) : ℝ)*M*E1*J := by ring
  have hLast : HolderBound α Q
      (fun p => v p*(∑ i, b p i*fderiv ℝ φ p.1 (Yau.realVec i)))
      (4*(Fintype.card (Yau.RIdx n) : ℝ)*M*E1*J) := by
    simpa only [hLastScale] using hLastRaw
  have hAll := holderBound_add (holderBound_add hFirst hMatrix) hLast
  have hScale :
      (4*(Fintype.card (Yau.RIdx n) : ℝ)*M*E0*J+
        (Fintype.card (Yau.RIdx n) : ℝ)^2*(8*M*E1*J+4*M*E2*J))+
        4*(Fintype.card (Yau.RIdx n) : ℝ)*M*E1*J =
      (4*(Fintype.card (Yau.RIdx n) : ℝ)*M*E0+
        8*(Fintype.card (Yau.RIdx n) : ℝ)^2*M*E1+
        4*(Fintype.card (Yau.RIdx n) : ℝ)^2*M*E2+
        4*(Fintype.card (Yau.RIdx n) : ℝ)*M*E1)*J := by ring
  change HolderBound α Q (fun p => lowerPatchResidual a b φ v p) _
  simpa only [lowerPatchResidual,hScale] using hAll

/-- Full frozen-patch error estimate. The highest-order term uses the
small coefficient sup bound; every commutator uses only the small low jet. -/
theorem frozenPatchResidual_holderBound {n : ℕ} {α A0 B C D M E0 E1 E2 J : ℝ}
    {Q : Set (Point n)} {a : Point n → Mat n} {b : Point n → Yau.RIdx n → ℝ}
    {A : Mat n} {φ : Space n → ℝ} {v : Point n → ℝ}
    (hA0 : 0 ≤ A0) (hD : 0 ≤ D)
    (ha : HolderBound α Q a M) (hb : ∀ i, HolderBound α Q (fun p => b p i) M)
    (hφ : HolderBound α Q (fun p => φ p.1) E0)
    (hφD : ∀ i : Yau.RIdx n,
      HolderBound α Q (fun p => fderiv ℝ φ p.1 (Yau.realVec i)) E1)
    (hφDD : ∀ i j : Yau.RIdx n, HolderBound α Q
      (fun p => fderiv ℝ (fderiv ℝ φ) p.1 (Yau.realVec i) (Yau.realVec j)) E2)
    (hJet : HolderBound α Q (fun p => (v p,spatialD v p)) J)
    (hHess : HolderBound α Q (spatialDD v) C)
    (hHessSup : ∀ p ∈ Q, ‖spatialDD v p‖ ≤ D)
    (hCoeff : ∀ i j : Yau.RIdx n,
      HolderBound α Q (fun p => φ p.1*(A i j-a p i j)) B)
    (hCoeffSup : ∀ i j : Yau.RIdx n, ∀ p ∈ Q, |φ p.1*(A i j-a p i j)| ≤ A0) :
    HolderBound α Q (frozenPatchResidual Q a b A φ v)
      ((Fintype.card (Yau.RIdx n) : ℝ)^2*(A0*C+B*D)+
        (4*(Fintype.card (Yau.RIdx n) : ℝ)*M*E0+
          8*(Fintype.card (Yau.RIdx n) : ℝ)^2*M*E1+
          4*(Fintype.card (Yau.RIdx n) : ℝ)^2*M*E2+
          4*(Fintype.card (Yau.RIdx n) : ℝ)*M*E1)*J) := by
  have hPrincipal := hessian_contraction_holderBound hA0 hD hCoeff hCoeffSup hHess hHessSup
  have hLower := lowerPatchResidual_holderBound ha hb hφ hφD hφDD hJet
  apply holderBound_congr_on (holderBound_sub hPrincipal hLower)
  intro p hp
  exact (frozenPatchResidual_eq_principal_sub_lower Q a b A φ v p).symm

theorem exterior_principal_coefficient_zero {n : ℕ} {Q : Set (Point n)}
    {K : Set (Space n)} {a : Point n → Mat n} (s : Finset (Space n))
    {r : ℝ} (hr : 0 < r) (hCover : ∀ x ∈ K, 1 ≤ patchSum s r hr x)
    (hExterior : ∀ p ∈ Q, p.1 ∉ K → a p = 1)
    {p : Point n} (hp : p ∈ Q) (i j : Yau.RIdx n) :
    exteriorCutoff s r hr p.1*((1 : Mat n) i j-a p i j) = 0 := by
  by_cases hx : p.1 ∈ K
  · rw [(exteriorCutoffs_zero_of_patchSum_ge_one s hr (hCover p.1 hx)).1,zero_mul]
  · rw [hExterior p hp hx,sub_self,mul_zero]

theorem exterior_frozenPatchResidual_eq_neg_lower {n : ℕ} {Q : Set (Point n)}
    {K : Set (Space n)} {a : Point n → Mat n} (b : Point n → Yau.RIdx n → ℝ)
    (s : Finset (Space n)) {r : ℝ} (hr : 0 < r)
    (hCover : ∀ x ∈ K, 1 ≤ patchSum s r hr x)
    (hExterior : ∀ p ∈ Q, p.1 ∉ K → a p = 1) (v : Point n → ℝ)
    {p : Point n} (hp : p ∈ Q) :
    frozenPatchResidual Q a b 1 (exteriorCutoff s r hr) v p =
      -lowerPatchResidual a b (exteriorCutoff s r hr) v p := by
  rw [frozenPatchResidual_eq_principal_sub_lower]
  simp only [exterior_principal_coefficient_zero s hr hCover hExterior hp,
    zero_mul,Finset.sum_const_zero,zero_sub]

theorem patchSum_hasCompactSupport {n : ℕ} (s : Finset (Space n)) {r : ℝ} (hr : 0 < r) :
    HasCompactSupport (patchSum s r hr) := by
  have h := HasCompactSupport.finset_sum
    (fun c (_ : c ∈ s) => (innerPatchBump r hr c).hasCompactSupport)
  have hFun : (∑ c ∈ s, (innerPatchBump r hr c : Space n → ℝ)) = patchSum s r hr := by
    funext x
    simp only [Finset.sum_apply,patchSum]
  simpa only [hFun] using h

/-- The single exterior patch has finite Holder jet budgets on the unit
slab. These may depend on the chosen finite localization and radius. -/
theorem exteriorCutoff_holder_jets {n : ℕ} {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (s : Finset (Space n)) {r : ℝ} (hr : 0 < r) :
    ∃ E0 E1 E2 : ℝ, 0 < E0 ∧ 0 < E1 ∧ 0 < E2 ∧
      HolderBound α (cylinder Set.univ 0 1) (fun p => exteriorCutoff s r hr p.1) E0 ∧
      HolderBound α (cylinder Set.univ 0 1) (fun p => fderiv ℝ (exteriorCutoff s r hr) p.1) E1 ∧
      HolderBound α (cylinder Set.univ 0 1)
        (fun p => fderiv ℝ (fderiv ℝ (exteriorCutoff s r hr)) p.1) E2 := by
  let K : Set (Space n) := tsupport (patchSum s r hr)
  have hK : IsCompact K := patchSum_hasCompactSupport s hr
  have hSpace := exteriorCutoff_contDiff s hr
  have hDSpace : ContDiff ℝ ∞ (fderiv ℝ (exteriorCutoff s r hr)) := hSpace.fderiv_right (by simp)
  have hDDSpace : ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ (exteriorCutoff s r hr))) :=
    hDSpace.fderiv_right (by simp)
  have hSmooth : ContDiff ℝ ∞ (fun p : Point n => exteriorCutoff s r hr p.1) :=
    hSpace.comp contDiff_fst
  have hDSmooth : ContDiff ℝ ∞ (fun p : Point n => fderiv ℝ (exteriorCutoff s r hr) p.1) :=
    hDSpace.comp contDiff_fst
  have hDDSmooth : ContDiff ℝ ∞
      (fun p : Point n => fderiv ℝ (fderiv ℝ (exteriorCutoff s r hr)) p.1) :=
    hDDSpace.comp contDiff_fst
  have hExterior : ∀ x ∉ K, ∀ t ∈ Set.Icc (0 : ℝ) 1, exteriorCutoff s r hr x = 1 := by
    intro x hx t ht
    have hZ : patchSum s r hr x = 0 := image_eq_zero_of_notMem_tsupport hx
    change exteriorPatchFactor (patchSum s r hr x) = 1
    rw [hZ]
    exact exteriorPatchFactor_eq_one (by norm_num)
  have hDExterior : ∀ x ∉ K, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      fderiv ℝ (exteriorCutoff s r hr) x = 0 := by
    intro x hx t ht
    apply ContinuousLinearMap.ext
    intro v
    have h := spatialPartial_eq_zero_of_exterior
      (g := fun p : Point n => exteriorCutoff s r hr p.1) (c := (1 : ℝ))
      hK hExterior v (p := (x,t)) ht hx
    simpa only [spatialPartial,zero_apply] using h
  have hDDExterior : ∀ x ∉ K, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      fderiv ℝ (fderiv ℝ (exteriorCutoff s r hr)) x = 0 := by
    intro x hx t ht
    apply ContinuousLinearMap.ext
    intro v
    have h := spatialPartial_eq_zero_of_exterior
      (g := fun p : Point n => fderiv ℝ (exteriorCutoff s r hr) p.1)
      (c := (0 : Space n →L[ℝ] ℝ)) hK hDExterior v (p := (x,t)) ht hx
    simpa only [spatialPartial,zero_apply] using h
  obtain ⟨E0,hE0,h0⟩ := smooth_cylinder_compact_perturbation_holder
    (by norm_num : (0 : ℝ) < 1) hα hα1 hK hSmooth.contDiffOn hExterior
  obtain ⟨E1,hE1,h1⟩ := smooth_cylinder_compact_perturbation_holder
    (by norm_num : (0 : ℝ) < 1) hα hα1 hK hDSmooth.contDiffOn hDExterior
  obtain ⟨E2,hE2,h2⟩ := smooth_cylinder_compact_perturbation_holder
    (by norm_num : (0 : ℝ) < 1) hα hα1 hK hDDSmooth.contDiffOn hDDExterior
  exact ⟨E0,E1,E2,hE0,hE1,hE2,h0,h1,h2⟩

theorem frozenPatchResidual_outer_zero_of_norm_gt {n : ℕ} (Q : Set (Point n))
    (a : Point n → Mat n) (b : Point n → Yau.RIdx n → ℝ) (A : Mat n)
    {r : ℝ} (hr : 0 < r) (c : Space n) (v : Point n → ℝ) {p : Point n}
    (hp : 2*r < ‖p.1-c‖) :
    frozenPatchResidual Q a b A (outerPatchBump r hr c) v p = 0 := by
  obtain ⟨hφ,hDφ,hDDφ⟩ := outerPatchBump_jets_zero_of_norm_gt hr hp
  simp only [frozenPatchResidual,hφ,hDφ,hDDφ,zero_apply,zero_mul,mul_zero,
    add_zero,Finset.sum_const_zero,sub_zero]

/-- The highest-order errors can be summed with a dimension-only loss,
which is the uniformity needed before choosing the localization radius. -/
theorem frozenPatchResidual_outer_sum_holderBound {n : ℕ} {α H : ℝ}
    {Q : Set (Point n)} (a : Point n → Mat n) (b : Point n → Yau.RIdx n → ℝ)
    (A : Space n → Mat n) (v : Space n → Point n → ℝ)
    {r : ℝ} (hr : 0 < r) (s : Finset (Space n))
    (hSep : ∀ c ∈ s, ∀ d ∈ s, c ≠ d → r ≤ ‖c-d‖) (hH : 0 ≤ H)
    (hResidual : ∀ c ∈ s,
      HolderBound α Q (frozenPatchResidual Q a b (A c) (outerPatchBump r hr c) (v c)) H) :
    HolderBound α Q
      (fun p => ∑ c ∈ s, frozenPatchResidual Q a b (A c) (outerPatchBump r hr c) (v c) p)
      (2*((5^(Module.finrank ℝ (Space n)) : ℕ) : ℝ)*H) := by
  classical
  apply holderBound_sum_boundedOverlap s hH hResidual
  intro p hp
  apply (Finset.card_le_card (show
    s.filter (fun c => frozenPatchResidual Q a b (A c) (outerPatchBump r hr c) (v c) p ≠ 0) ⊆
      s.filter (fun c => ‖c-p.1‖ ≤ 2*r) from ?_)).trans
    (separated_centers_overlap_bound hr s hSep p.1)
  intro c hc
  obtain ⟨hcs,hNonzero⟩ := Finset.mem_filter.mp hc
  refine Finset.mem_filter.mpr ⟨hcs,?_⟩
  rw [norm_sub_rev]
  by_contra hNorm
  exact hNonzero (frozenPatchResidual_outer_zero_of_norm_gt Q a b (A c) hr c (v c)
    (lt_of_not_ge hNorm))

end Yau.LeafProofs.L16Aux
