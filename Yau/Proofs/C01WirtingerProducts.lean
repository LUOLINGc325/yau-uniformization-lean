import Yau.Proofs.Y03LeviQuadratic

/-!
Product calculus for the actual C01 inverse-metric jets.  The domain can be
the genuine product of the spatial chart and logarithmic time.  This keeps
the calculation independent of any positive-time completeness statement.
-/

noncomputable section

open scoped Topology ContDiff Matrix
open Filter

namespace Yau.NodeProofs.C01Aux

open Yau
open Yau.Blueprint.Alignment.Y03Proof

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem wirt_product {f g : V → ℂ} {z : V}
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) (v : V) :
    wirt (fun p => f p * g p) z v =
      wirt f z v * g z + f z * wirt g z v := by
  unfold wirt
  rw [fderiv_fun_mul hf hg]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem wirtBar_product {f g : V → ℂ} {z : V}
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) (v : V) :
    wirtBar (fun p => f p * g p) z v =
      wirtBar f z v * g z + f z * wirtBar g z v := by
  unfold wirtBar
  rw [fderiv_fun_mul hf hg]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem wirt_congr_germ {f g : V → ℂ} {z : V}
    (hfg : f =ᶠ[𝓝 z] g) (v : V) : wirt f z v = wirt g z v := by
  unfold wirt
  rw [hfg.fderiv_eq]

theorem wirtBar_congr_germ {f g : V → ℂ} {z : V}
    (hfg : f =ᶠ[𝓝 z] g) (v : V) : wirtBar f z v = wirtBar g z v := by
  unfold wirtBar
  rw [hfg.fderiv_eq]

theorem wirt_wirtBar_congr_germ {f g : V → ℂ} {z : V}
    (hfg : f =ᶠ[𝓝 z] g) (v w : V) :
    wirt (fun p => wirtBar f p v) z w =
      wirt (fun p => wirtBar g p v) z w := by
  apply wirt_congr_germ
  filter_upwards [hfg.eventuallyEq_nhds] with p hp
  exact wirtBar_congr_germ hp v

theorem wirtBar_fintype_sum {ι : Type*} [Fintype ι]
    (f : ι → V → ℂ) (z v : V)
    (hf : ∀ i, DifferentiableAt ℝ (f i) z) :
    wirtBar (fun p => ∑ i, f i p) z v = ∑ i, wirtBar (f i) z v := by
  unfold wirtBar
  rw [fderiv_fun_sum (fun i _ => hf i)]
  simp only [sum_apply, mul_add, Finset.mul_sum, Finset.sum_add_distrib, mul_assoc]

theorem wirt_wirtBar_fintype_sum {ι : Type*} [Fintype ι]
    (f : ι → V → ℂ) (z v w : V)
    (hf : ∀ i, ContDiffAt ℝ 2 (f i) z) :
    wirt (fun p => wirtBar (fun q => ∑ i, f i q) p v) z w =
      ∑ i, wirt (fun p => wirtBar (f i) p v) z w := by
  have hnear : ∀ᶠ p in 𝓝 z, ∀ i, ContDiffAt ℝ 2 (f i) p :=
    eventually_all.mpr (fun i => (hf i).eventually (by norm_num))
  have hinner : (fun p => wirtBar (fun q => ∑ i, f i q) p v) =ᶠ[𝓝 z]
      (fun p => ∑ i, wirtBar (f i) p v) := by
    filter_upwards [hnear] with p hp
    exact wirtBar_fintype_sum f p v (fun i => (hp i).differentiableAt (by norm_num))
  rw [wirt_congr_germ hinner w]
  exact wirt_sum_fn Finset.univ _
    (fun i _ => (wirtBar_contDiffAt (hf i) v).differentiableAt (by norm_num)) w

/-- The mixed product rule keeps both ordered cross terms. -/
theorem wirt_wirtBar_product {f g : V → ℂ} {z : V}
    (hf : ContDiffAt ℝ 2 f z) (hg : ContDiffAt ℝ 2 g z) (v w : V) :
    wirt (fun p => wirtBar (fun q => f q * g q) p v) z w =
      wirt (fun p => wirtBar f p v) z w * g z +
      wirtBar f z v * wirt g z w + wirt f z w * wirtBar g z v +
      f z * wirt (fun p => wirtBar g p v) z w := by
  have hfg : (fun p => wirtBar (fun q => f q * g q) p v) =ᶠ[𝓝 z]
      (fun p => wirtBar f p v * g p + f p * wirtBar g p v) := by
    filter_upwards [hf.eventually (by norm_num), hg.eventually (by norm_num)] with p hp hq
    exact wirtBar_product (hp.differentiableAt (by norm_num))
      (hq.differentiableAt (by norm_num)) v
  have hfd : DifferentiableAt ℝ f z := hf.differentiableAt (by norm_num)
  have hgd : DifferentiableAt ℝ g z := hg.differentiableAt (by norm_num)
  have hfbar : DifferentiableAt ℝ (fun p => wirtBar f p v) z :=
    (wirtBar_contDiffAt hf v).differentiableAt (by norm_num)
  have hgbar : DifferentiableAt ℝ (fun p => wirtBar g p v) z :=
    (wirtBar_contDiffAt hg v).differentiableAt (by norm_num)
  have hsum : wirt (fun p => wirtBar f p v * g p + f p * wirtBar g p v) z w =
      wirt (fun p => wirtBar f p v * g p) z w +
        wirt (fun p => f p * wirtBar g p v) z w :=
    wirt_add_fn (f := fun p => wirtBar f p v * g p)
      (g := fun p => f p * wirtBar g p v) (hfbar.mul hgd) (hfd.mul hgbar) w
  have hmul₁ : wirt (fun p => wirtBar f p v * g p) z w =
      wirt (fun p => wirtBar f p v) z w * g z + wirtBar f z v * wirt g z w :=
    wirt_product hfbar hgd w
  have hmul₂ : wirt (fun p => f p * wirtBar g p v) z w =
      wirt f z w * wirtBar g z v + f z * wirt (fun p => wirtBar g p v) z w :=
    wirt_product hfd hgbar w
  rw [wirt_congr_germ hfg w, hsum, hmul₁, hmul₂]
  ring

/-- The matrix product rule for an arbitrary genuine complex base
direction, rather than a separately postulated connection tensor. -/
theorem matrix_wirt_product {n : ℕ} (A B : V → Matrix (Fin n) (Fin n) ℂ)
    (z v : V)
    (hA : ∀ i j, DifferentiableAt ℝ (fun p => A p i j) z)
    (hB : ∀ i j, DifferentiableAt ℝ (fun p => B p i j) z) :
    (Matrix.of fun i j => wirt (fun p => (A p * B p) i j) z v) =
      (Matrix.of fun i j => wirt (fun p => A p i j) z v) * B z +
        A z * (Matrix.of fun i j => wirt (fun p => B p i j) z v) := by
  let a : V → Fin n → Fin n → ℂ := fun p => Matrix.of.symm (A p)
  let b : V → Fin n → Fin n → ℂ := fun p => Matrix.of.symm (B p)
  have ha (i j : Fin n) : DifferentiableAt ℝ (fun p => a p i j) z := hA i j
  have hb (i j : Fin n) : DifferentiableAt ℝ (fun p => b p i j) z := hB i j
  ext i j
  change wirt (fun p => ∑ k, a p i k * b p k j) z v =
    (∑ k, wirt (fun p => a p i k) z v * b z k j) +
      ∑ k, a z i k * wirt (fun p => b p k j) z v
  rw [wirt_sum_fn Finset.univ (fun k p => a p i k * b p k j)
    (fun k _ => (ha i k).mul (hb k j)) v]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  exact wirt_product (ha i k) (hb k j) v

theorem matrix_wirtBar_product {n : ℕ} (A B : V → Matrix (Fin n) (Fin n) ℂ)
    (z v : V)
    (hA : ∀ i j, DifferentiableAt ℝ (fun p => A p i j) z)
    (hB : ∀ i j, DifferentiableAt ℝ (fun p => B p i j) z) :
    (Matrix.of fun i j => wirtBar (fun p => (A p * B p) i j) z v) =
      (Matrix.of fun i j => wirtBar (fun p => A p i j) z v) * B z +
        A z * (Matrix.of fun i j => wirtBar (fun p => B p i j) z v) := by
  let a : V → Fin n → Fin n → ℂ := fun p => Matrix.of.symm (A p)
  let b : V → Fin n → Fin n → ℂ := fun p => Matrix.of.symm (B p)
  have ha (i j : Fin n) : DifferentiableAt ℝ (fun p => a p i j) z := hA i j
  have hb (i j : Fin n) : DifferentiableAt ℝ (fun p => b p i j) z := hB i j
  ext i j
  change wirtBar (fun p => ∑ k, a p i k * b p k j) z v =
    (∑ k, wirtBar (fun p => a p i k) z v * b z k j) +
      ∑ k, a z i k * wirtBar (fun p => b p k j) z v
  have hsum : wirtBar (fun p => ∑ k, a p i k * b p k j) z v =
      ∑ k, wirtBar (fun p => a p i k * b p k j) z v := by
    unfold wirtBar
    rw [fderiv_fun_sum (u := Finset.univ) (A := fun k p => a p i k * b p k j)
      (fun k _ => (ha i k).mul (hb k j))]
    simp only [sum_apply, mul_add, Finset.mul_sum, Finset.sum_add_distrib, mul_assoc]
  rw [hsum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  exact wirtBar_product (ha i k) (hb k j) v

theorem matrix_wirt_wirtBar_product {n : ℕ}
    (A B : V → Matrix (Fin n) (Fin n) ℂ) (z v w : V)
    (hA : ∀ i j, ContDiffAt ℝ 2 (fun p => A p i j) z)
    (hB : ∀ i j, ContDiffAt ℝ 2 (fun p => B p i j) z) :
    (Matrix.of fun i j => wirt (fun p => wirtBar (fun q => (A q * B q) i j) p v) z w) =
      (Matrix.of fun i j => wirt (fun p => wirtBar (fun q => A q i j) p v) z w) * B z +
      (Matrix.of fun i j => wirtBar (fun p => A p i j) z v) *
        (Matrix.of fun i j => wirt (fun p => B p i j) z w) +
      (Matrix.of fun i j => wirt (fun p => A p i j) z w) *
        (Matrix.of fun i j => wirtBar (fun p => B p i j) z v) +
      A z * (Matrix.of fun i j => wirt (fun p => wirtBar (fun q => B q i j) p v) z w) := by
  ext i j
  change wirt (fun p => wirtBar (fun q => ∑ k, A q i k * B q k j) p v) z w = _
  rw [wirt_wirtBar_fintype_sum (fun k p => A p i k * B p k j) z v w
    (fun k => (hA i k).mul (hB k j))]
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.of_apply]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  exact wirt_wirtBar_product (hA i k) (hB k j) v w

end Yau.NodeProofs.C01Aux
