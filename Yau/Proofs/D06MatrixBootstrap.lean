import Yau.Proofs.D06MatrixBootstrapFixedB

/-! The paper's original all-order bootstrap for one fixed Hardy pair.
The angular derivative is the actual multiplier i*n, and the same
B=(D h)p is recovered by the strictly positive Fourier projection at
every order.  No new factor, derivative field, or B-regularity premise
occurs in the theorem. -/

open MeasureTheory
open scoped Matrix

noncomputable section
namespace Yau.NodeProofs.D06Aux

theorem circleMatrix_fixedB_sobolev {r : ℕ} (L h p : CircleMatrix r)
    (hL : ∀ k, CircleMatrixSobolev k L)
    (hh1 : CircleMatrixSobolev 1 h) (hp1 : CircleMatrixSobolev 1 p)
    (hhHardy : CircleMatrixHardy h) (hpHardy : CircleMatrixHardy p)
    (hInv : ∀ᵐ t ∂hardyCircleMeasure,
      circleMatrixEval h t * circleMatrixEval p t = 1 ∧
        circleMatrixEval p t * circleMatrixEval h t = 1)
    (hGram : ∀ᵐ t ∂hardyCircleMeasure,
      circleMatrixEval L t = (circleMatrixEval h t)ᴴ * circleMatrixEval h t)
    (k : ℕ) (hk : 1 ≤ k) (hpk : CircleMatrixSobolev k p) :
    CircleMatrixSobolev k (circleMatrixProduct (circleMatrixDerivative h hh1) p) := by
  let dh := circleMatrixDerivative h hh1
  let dl := circleMatrixDerivative L (hL 1)
  let B := circleMatrixProduct dh p
  let C := circleMatrixProduct (circleMatrixProduct (circleMatrixStar p) dl) p
  have hdl (l : ℕ) : CircleMatrixSobolev l dl := by
    intro i j
    exact circleDerivative_sobolev l (hL (l + 1) i j)
  have hCk : CircleMatrixSobolev k C :=
    circleMatrixSobolev_product hk
      (circleMatrixSobolev_product hk (circleMatrixSobolev_star hpk) (hdl k)) hpk
  have hCeq : C = B + circleMatrixStar B := by
    apply circleMatrix_ext_ae
    have hS := (circleMatrix_fixedPair_derivative_identities L h p (hL 1) hh1 hp1 hInv hGram).1
    filter_upwards [circleMatrixProduct_ae (circleMatrixProduct (circleMatrixStar p) dl) p hp1,
      circleMatrixProduct_ae (circleMatrixStar p) dl (hdl 1), circleMatrixStar_ae p,
      hS, circleMatrix_add_ae B (circleMatrixStar B), circleMatrixStar_ae B]
      with t houter hinner hstar hs hadd hBstar
    calc
      circleMatrixEval C t = (circleMatrixEval p t)ᴴ * circleMatrixEval dl t *
          circleMatrixEval p t := by rw [houter, hinner, hstar]
      _ = circleMatrixEval B t + (circleMatrixEval B t)ᴴ := hs
      _ = circleMatrixEval (B + circleMatrixStar B) t := by rw [hadd, hBstar]
  have hpos := circleMatrix_fixedB_positive h p hh1 hp1 hhHardy hpHardy
  intro i j
  have hrec : circlePositiveProjection (C i j) = B i j :=
    circlePositiveProjection_pair_recover (B i j) (B j i) (C i j)
      (hpos i j) (hpos j i) (congrFun (congrFun hCeq i) j)
  change CircleSobolev k (B i j)
  rw [← hrec]
  exact circlePositiveProjection_sobolev (hCk i j)

theorem circleMatrix_fixedPair_allSobolev {r : ℕ} (L h p : CircleMatrix r)
    (hL : ∀ k, CircleMatrixSobolev k L)
    (hh1 : CircleMatrixSobolev 1 h) (hp1 : CircleMatrixSobolev 1 p)
    (hhHardy : CircleMatrixHardy h) (hpHardy : CircleMatrixHardy p)
    (hInv : ∀ᵐ t ∂hardyCircleMeasure,
      circleMatrixEval h t * circleMatrixEval p t = 1 ∧
        circleMatrixEval p t * circleMatrixEval h t = 1)
    (hGram : ∀ᵐ t ∂hardyCircleMeasure,
      circleMatrixEval L t = (circleMatrixEval h t)ᴴ * circleMatrixEval h t) :
    ∀ k, CircleMatrixSobolev k h ∧ CircleMatrixSobolev k p := by
  let dh := circleMatrixDerivative h hh1
  let dp := circleMatrixDerivative p hp1
  let B := circleMatrixProduct dh p
  have hB (k : ℕ) (hk : 1 ≤ k) (hpk : CircleMatrixSobolev k p) : CircleMatrixSobolev k B :=
    circleMatrix_fixedB_sobolev L h p hL hh1 hp1 hhHardy hpHardy hInv hGram k hk hpk
  have hid := (circleMatrix_fixedPair_derivative_identities L h p (hL 1) hh1 hp1 hInv hGram).2
  have hdh : dh = circleMatrixProduct B h := by
    apply circleMatrix_ext_ae
    filter_upwards [hid, circleMatrixProduct_ae B h hh1] with t ht hp
    exact ht.1.trans hp.symm
  have hdp : dp = -circleMatrixProduct p B := by
    apply circleMatrix_ext_ae
    filter_upwards [hid, circleMatrixProduct_ae p B (hB 1 le_rfl hp1),
      circleMatrix_neg_ae (circleMatrixProduct p B)] with t ht hp hn
    exact ht.2.trans (by rw [hn, hp])
  have hs : ∀ k, CircleMatrixSobolev (k + 1) h ∧ CircleMatrixSobolev (k + 1) p := by
    intro k
    induction k with
    | zero => exact ⟨hh1, hp1⟩
    | succ k ih =>
      have hBk := hB (k + 1) (by omega) ih.2
      have hdhk : CircleMatrixSobolev (k + 1) dh := by
        rw [hdh]
        exact circleMatrixSobolev_product (by omega) hBk ih.1
      have hdpk : CircleMatrixSobolev (k + 1) dp := by
        rw [hdp]
        intro i j
        exact circleSobolev_neg (circleMatrixSobolev_product (by omega) ih.2 hBk i j)
      constructor
      · intro i j
        exact circleSobolev_succ_of_derivative (k + 1)
          (circleMatrixDerivative_weak h hh1 i j) (ih.1 i j) (hdhk i j)
      · intro i j
        exact circleSobolev_succ_of_derivative (k + 1)
          (circleMatrixDerivative_weak p hp1 i j) (ih.2 i j) (hdpk i j)
  intro k
  cases k with
  | zero => exact ⟨fun _ _ => circleSobolev_zero _, fun _ _ => circleSobolev_zero _⟩
  | succ k => exact hs k

end Yau.NodeProofs.D06Aux
