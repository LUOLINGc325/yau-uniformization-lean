import Yau.Proofs.D06CircleLinearCalculus

/-! Matrix versions of the actual angular Fourier weak calculus.  Products
remain in the original circle L² classes, and are identified with their
pointwise matrix products only through the proved Sobolev representative. -/

open MeasureTheory
open scoped ComplexConjugate Matrix

noncomputable section
namespace Yau.NodeProofs.D06Aux

abbrev CircleMatrix (r : ℕ) := Matrix (Fin r) (Fin r) CircleL2

def circleMatrixEval {r : ℕ} (A : CircleMatrix r) (t : HardyCircle) :
    Matrix (Fin r) (Fin r) ℂ := fun i j => A i j t

def CircleMatrixSobolev {r : ℕ} (k : ℕ) (A : CircleMatrix r) : Prop :=
  ∀ i j, CircleSobolev k (A i j)

def CircleMatrixHardy {r : ℕ} (A : CircleMatrix r) : Prop :=
  ∀ i j (n : ℤ), n < 0 → circleCoeff (A i j) n = 0

def CircleMatrixWeakDerivative {r : ℕ} (A DA : CircleMatrix r) : Prop :=
  ∀ i j, CircleWeakDerivative (A i j) (DA i j)

def circleMatrixDerivative {r : ℕ} (A : CircleMatrix r)
    (hA : CircleMatrixSobolev 1 A) : CircleMatrix r :=
  fun i j => circleDerivative (A i j) (hA i j)

def circleMatrixProduct {r : ℕ} (A B : CircleMatrix r) : CircleMatrix r :=
  fun i j => ∑ k, circleProduct (A i k) (B k j)

def circleMatrixStar {r : ℕ} (A : CircleMatrix r) : CircleMatrix r :=
  fun i j => star (A j i)

def circleMatrixLeibniz {r : ℕ} (A B DA DB : CircleMatrix r) : CircleMatrix r :=
  fun i j => ∑ k, (circleProduct (DA i k) (B k j) + circleProduct (DB k j) (A i k))

theorem circleMatrix_ext_ae {r : ℕ} {A B : CircleMatrix r}
    (h : circleMatrixEval A =ᵐ[hardyCircleMeasure] circleMatrixEval B) : A = B := by
  funext i j
  apply Lp.ext
  filter_upwards [h] with t ht
  exact congrFun (congrFun ht i) j

theorem circleMatrixProduct_ae {r : ℕ} (A B : CircleMatrix r)
    (hB : CircleMatrixSobolev 1 B) :
    circleMatrixEval (circleMatrixProduct A B) =ᵐ[hardyCircleMeasure]
      fun t => circleMatrixEval A t * circleMatrixEval B t := by
  have hsum : ∀ᵐ t ∂hardyCircleMeasure, ∀ i j,
      (∑ k, circleProduct (A i k) (B k j)) t =
        ∑ k, circleProduct (A i k) (B k j) t :=
    ae_all_iff.mpr (fun i => ae_all_iff.mpr (fun j => Lp.coeFn_fun_finsetSum _ _))
  have hmul : ∀ᵐ t ∂hardyCircleMeasure, ∀ i k j,
      circleProduct (A i k) (B k j) t = A i k t * B k j t :=
    ae_all_iff.mpr (fun i => ae_all_iff.mpr (fun k => ae_all_iff.mpr
      (fun j => circleProduct_ae _ _ (hB k j))))
  filter_upwards [hsum, hmul] with t hs hm
  funext i j
  exact (hs i j).trans (Finset.sum_congr rfl (fun k _ => hm i k j))

theorem circleMatrixStar_ae {r : ℕ} (A : CircleMatrix r) :
    circleMatrixEval (circleMatrixStar A) =ᵐ[hardyCircleMeasure]
      fun t => (circleMatrixEval A t)ᴴ := by
  have h : ∀ᵐ t ∂hardyCircleMeasure, ∀ i j, star (A j i) t = star (A j i t) :=
    ae_all_iff.mpr (fun i => ae_all_iff.mpr (fun j => Lp.coeFn_star _))
  filter_upwards [h] with t ht
  funext i j
  exact ht i j

theorem circleMatrix_add_ae {r : ℕ} (A B : CircleMatrix r) :
    circleMatrixEval (A + B) =ᵐ[hardyCircleMeasure]
      fun t => circleMatrixEval A t + circleMatrixEval B t := by
  have h : ∀ᵐ t ∂hardyCircleMeasure, ∀ i j, (A i j + B i j) t = A i j t + B i j t :=
    ae_all_iff.mpr (fun i => ae_all_iff.mpr (fun j => Lp.coeFn_add _ _))
  filter_upwards [h] with t ht
  funext i j
  exact ht i j

theorem circleMatrix_neg_ae {r : ℕ} (A : CircleMatrix r) :
    circleMatrixEval (-A) =ᵐ[hardyCircleMeasure] fun t => -circleMatrixEval A t := by
  have h : ∀ᵐ t ∂hardyCircleMeasure, ∀ i j, (-A i j) t = -(A i j t) :=
    ae_all_iff.mpr (fun i => ae_all_iff.mpr (fun j => Lp.coeFn_neg _))
  filter_upwards [h] with t ht
  funext i j
  exact ht i j

theorem circleMatrixLeibniz_ae {r : ℕ} (A B DA DB : CircleMatrix r)
    (hA : CircleMatrixSobolev 1 A) (hB : CircleMatrixSobolev 1 B) :
    circleMatrixEval (circleMatrixLeibniz A B DA DB) =ᵐ[hardyCircleMeasure]
      fun t => circleMatrixEval DA t * circleMatrixEval B t +
        circleMatrixEval A t * circleMatrixEval DB t := by
  have hsum : ∀ᵐ t ∂hardyCircleMeasure, ∀ i j,
      (∑ k, (circleProduct (DA i k) (B k j) + circleProduct (DB k j) (A i k))) t =
        ∑ k, (circleProduct (DA i k) (B k j) + circleProduct (DB k j) (A i k)) t :=
    ae_all_iff.mpr (fun i => ae_all_iff.mpr (fun j => Lp.coeFn_fun_finsetSum _ _))
  have hadd : ∀ᵐ t ∂hardyCircleMeasure, ∀ i k j,
      (circleProduct (DA i k) (B k j) + circleProduct (DB k j) (A i k)) t =
        circleProduct (DA i k) (B k j) t + circleProduct (DB k j) (A i k) t :=
    ae_all_iff.mpr (fun i => ae_all_iff.mpr (fun k => ae_all_iff.mpr
      (fun j => Lp.coeFn_add _ _)))
  have hmul₁ : ∀ᵐ t ∂hardyCircleMeasure, ∀ i k j,
      circleProduct (DA i k) (B k j) t = DA i k t * B k j t :=
    ae_all_iff.mpr (fun i => ae_all_iff.mpr (fun k => ae_all_iff.mpr
      (fun j => circleProduct_ae _ _ (hB k j))))
  have hmul₂ : ∀ᵐ t ∂hardyCircleMeasure, ∀ i k j,
      circleProduct (DB k j) (A i k) t = DB k j t * A i k t :=
    ae_all_iff.mpr (fun i => ae_all_iff.mpr (fun k => ae_all_iff.mpr
      (fun j => circleProduct_ae _ _ (hA i k))))
  filter_upwards [hsum, hadd, hmul₁, hmul₂] with t hs ha hm₁ hm₂
  funext i j
  change (∑ k, (circleProduct (DA i k) (B k j) + circleProduct (DB k j) (A i k))) t =
    (∑ k, DA i k t * B k j t) + ∑ k, A i k t * DB k j t
  rw [hs i j, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rw [ha i k j, hm₁ i k j, hm₂ i k j, mul_comm (DB k j t)]

theorem circleMatrixDerivative_weak {r : ℕ} (A : CircleMatrix r)
    (hA : CircleMatrixSobolev 1 A) :
    CircleMatrixWeakDerivative A (circleMatrixDerivative A hA) :=
  fun _ _ => circleDerivative_weak _ _

theorem circleMatrixWeakDerivative_product {r : ℕ} {A B DA DB : CircleMatrix r}
    (hA : CircleMatrixSobolev 1 A) (hB : CircleMatrixSobolev 1 B)
    (hDA : CircleMatrixWeakDerivative A DA) (hDB : CircleMatrixWeakDerivative B DB) :
    CircleMatrixWeakDerivative (circleMatrixProduct A B) (circleMatrixLeibniz A B DA DB) := by
  intro i j
  exact circleWeakDerivative_finsetSum _ _ _
    (fun k _ => circleWeakDerivative_product (hA i k) (hB k j) (hDA i k) (hDB k j))

theorem circleMatrixWeakDerivative_star {r : ℕ} {A DA : CircleMatrix r}
    (h : CircleMatrixWeakDerivative A DA) :
    CircleMatrixWeakDerivative (circleMatrixStar A) (circleMatrixStar DA) :=
  fun i j => circleWeakDerivative_star (h j i)

theorem circleMatrixSobolev_mono {r k l : ℕ} {A : CircleMatrix r}
    (hA : CircleMatrixSobolev l A) (hkl : k ≤ l) : CircleMatrixSobolev k A :=
  fun i j => circleSobolev_mono (hA i j) hkl

theorem circleMatrixSobolev_star {r k : ℕ} {A : CircleMatrix r}
    (hA : CircleMatrixSobolev k A) : CircleMatrixSobolev k (circleMatrixStar A) :=
  fun i j => circleSobolev_star (hA j i)

theorem circleMatrixSobolev_product {r k : ℕ} {A B : CircleMatrix r}
    (hk : 1 ≤ k) (hA : CircleMatrixSobolev k A) (hB : CircleMatrixSobolev k B) :
    CircleMatrixSobolev k (circleMatrixProduct A B) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  intro i j
  exact circleSobolev_finsetSum _ _ _ (fun l _ => circleProduct_sobolev_succ k (hA i l) (hB l j))

end Yau.NodeProofs.D06Aux
