import Percolation.Literature.SlabUniqueness
import Percolation.Util.Linter

/-!
# DST 2016, Thm. 1 from the Gluing Lemma in the range `u_{3n} + 1 ≤ n`

The paper's sequence `(u_n)` of eq. (1) is only
required to satisfy `u_n ≤ n/3` and `P[B_{u_n} ⟷^{!B_n!} ∂B_n] → 1`; the diagonal extraction of
`SlabCriticalityInputs.lean` gives `u_n ≤ n/4` just as well (`exists_seq_tendsto_one_of_liminf4`),
and then `u_{3n} ≤ 3n/4 < n`.

* `…_eq1'`, `…_eq12'`, `…_eq13'` — eq. (1), (12), (13) for sequences with `4 u_n ≤ n`; proved:
  `…_eq1'_of_uniqueCluster`, `…_eq12'_of_lemmas` (from Lemma 4 and Lemma 6'),
  `…_eq13'_of_eq12'`, `…_goodEvent_likely_of_eq1'_eq13'` — the proofs of `SlabCriticality.lean`
  and `SlabCriticalityInputs.lean` verbatim up to the constant `3 ↦ 4` and the scale `n ≥ 4`.
* `DuminilCopinSidoraviciusTassion2016.of_lemma6'` — proved: Thm. 1 from Lemma 6' alone.

## Sources

* H. Duminil-Copin, V. Sidoravicius, V. Tassion, *Absence of infinite cluster for critical
  Bernoulli percolation on slabs*, CPAM 69 (2016), arXiv:1401.7130: §2.1 (eq. (1), Lemmata 4–6,
  eqs. (10)–(13)), §2.2.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal

namespace Percolation.Literature

open LatticeModels

/-! ## The statements -/

/-- Users take `(h : DuminilCopinSidoraviciusTassion2016_lemma6')`. [cite:
 DuminilCopinSidoraviciusTassion2016, Lemma 6]
-/
def DuminilCopinSidoraviciusTassion2016_lemma6' : Prop :=
  ∀ k : ℕ, 0 < k → ∀ p : unitInterval, 0 < theta (slabGraph 3 k) (slabOrigin 3 k) p →
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ (n u₃ u₁ α : ℕ) (y : ℤ), 2 ≤ n → u₃ + 1 ≤ n → 3 * u₁ ≤ n → 1 ≤ α → α + 1 ≤ n →
        0 ≤ y → y ≤ 3 * n →
        1 - δ ≤ (bondPercolation (slabGraph 3 k) p).real
          (slabConn k (sqBox 0 (3 * n)) (sqBox 0 u₃) (sideSeg (3 * n) (y - α) (y + α)) ∩
            slabConn k (sqBox (2 * (n : ℤ), y) n) (sqBox (2 * (n : ℤ), y) u₁)
              (sideSeg (3 * n) (y - n) (y - α)) ∩
            slabConn k (sqBox (2 * (n : ℤ), y) n) (sqBox (2 * (n : ℤ), y) u₁)
              (sideSeg (3 * n) (y + α) (y + n))) →
        1 - ε ≤ (bondPercolation (slabGraph 3 k) p).real
          (slabConn k (sqBox 0 (3 * n) ∪ sqBox (2 * (n : ℤ), y) n) (sqBox 0 u₃)
            (sqBox (2 * (n : ℤ), y) u₁))

/-- **DST 2016, §2.1, eq. (1)** with the (equally admissible) normalisation `u_n ≤ n/4`.
Users take `(h : DuminilCopinSidoraviciusTassion2016_eq1')`. [cite: DuminilCopinSidoraviciusTassion2016, §2.1 eq. (1)] -/
def DuminilCopinSidoraviciusTassion2016_eq1' : Prop :=
  ∀ k : ℕ, 0 < k → ∀ p : unitInterval, 0 < theta (slabGraph 3 k) (slabOrigin 3 k) p →
    ∃ u : ℕ → ℕ, (∀ n, 4 * u n ≤ n) ∧
      Tendsto (fun n => (bondPercolation (slabGraph 3 k) p).real
        (slabUniqueConn k (sqBox 0 n) (sqBox 0 (u n)) (sqSphere 0 n))) atTop (nhds 1)

/-- **DST 2016, §2.1, eq. (12)** for sequences with `u_n ≤ n/4`. [cite:
 DuminilCopinSidoraviciusTassion2016, §2.1 eq. (12)]
-/
def DuminilCopinSidoraviciusTassion2016_eq12' : Prop :=
  ∀ k : ℕ, 0 < k → ∀ p : unitInterval, 0 < theta (slabGraph 3 k) (slabOrigin 3 k) p →
    ∀ u : ℕ → ℕ, (∀ n, 4 * u n ≤ n) →
      Tendsto (fun n => (bondPercolation (slabGraph 3 k) p).real
        (slabUniqueConn k (sqBox 0 n) (sqBox 0 (u n)) (sqSphere 0 n))) atTop (nhds 1) →
      ∃ y : ℕ → ℤ, (∀ n, 1 ≤ n → 0 ≤ y n ∧ y n ≤ n) ∧
        ∀ ε : ℝ, 0 < ε → ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
          1 - ε < (bondPercolation (slabGraph 3 k) p).real
            (slabConn k (sqBox 0 (4 * n)) (sqBox 0 (u (3 * n))) (sqBox (2 * (n : ℤ), y (3 * n)) (u n)))

/-- **DST 2016, §2.1, eq. (13)** for sequences with `u_n ≤ n/4`. [cite:
 DuminilCopinSidoraviciusTassion2016, §2.1 eq. (13)]
-/
def DuminilCopinSidoraviciusTassion2016_eq13' : Prop :=
  ∀ k : ℕ, 0 < k → ∀ p : unitInterval, 0 < theta (slabGraph 3 k) (slabOrigin 3 k) p →
    ∀ u : ℕ → ℕ, (∀ n, 4 * u n ≤ n) →
      Tendsto (fun n => (bondPercolation (slabGraph 3 k) p).real
        (slabUniqueConn k (sqBox 0 n) (sqBox 0 (u n)) (sqSphere 0 n))) atTop (nhds 1) →
      ∀ ε : ℝ, 0 < ε → ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
        1 - ε < (bondPercolation (slabGraph 3 k) p).real
          (slabConn k (sqBox (2 * (n : ℤ), 0) (6 * n)) (sqBox 0 (u (3 * n)))
            (sqBox (4 * (n : ℤ), 0) (u (3 * n))))

/-! ## eq. (1) with `u_n ≤ n/4` -/

/-- **Diagonal extraction** with the normalisation `4 u_n ≤ n`. [cite:
 DuminilCopinSidoraviciusTassion2016, §2.1 (eq. (1))]
-/
theorem exists_seq_tendsto_one_of_liminf4 {a : ℕ → ℕ → ℝ} {g : ℕ → ℝ}
    (ha0 : ∀ v n, 0 ≤ a v n) (ha1 : ∀ v n, a v n ≤ 1) (hg1 : ∀ v, g v ≤ 1)
    (hlim : ∀ v, ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, g v - ε ≤ a v n)
    (hg : Tendsto g atTop (nhds 1)) :
    ∃ u : ℕ → ℕ, (∀ n, 4 * u n ≤ n) ∧ Tendsto (fun n => a (u n) n) atTop (nhds 1) := by
  classical
  -- `Q v n`: the radius `v` is admissible at time `n`
  let Q : ℕ → ℕ → Prop := fun v n =>
    4 * v ≤ n ∧ ∀ m, n ≤ m → ∀ w, w ≤ v → g w - 1 / ((w : ℝ) + 1) ≤ a w m
  have hQ0 : ∀ n, Q 0 n := by
    intro n
    refine ⟨by simp, fun m _ w hw => ?_⟩
    obtain rfl : w = 0 := Nat.le_zero.1 hw
    have h1 := hg1 0
    have h2 := ha0 0 m
    norm_num
    linarith
  let u : ℕ → ℕ := fun n => Nat.findGreatest (fun v => Q v n) n
  have hspec : ∀ n, Q (u n) n := fun n =>
    Nat.findGreatest_spec (P := fun v => Q v n) (Nat.zero_le n) (hQ0 n)
  refine ⟨u, fun n => (hspec n).1, ?_⟩
  -- `u_n → ∞`
  have hu : Tendsto u atTop atTop := by
    refine Filter.tendsto_atTop_atTop.2 fun v => ?_
    have hev : ∀ w ∈ {w | w ≤ v}, ∀ᶠ n in atTop, g w - 1 / ((w : ℝ) + 1) ≤ a w n :=
      fun w _ => hlim w (1 / ((w : ℝ) + 1)) (by positivity)
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 ((Set.finite_le_nat v).eventually_all.2 hev)
    refine ⟨max N (4 * v), fun n hn => ?_⟩
    have hQ : Q v n :=
      ⟨le_of_max_le_right hn, fun m hm w hw => hN m (le_of_max_le_left (hn.trans hm)) w hw⟩
    exact Nat.le_findGreatest (P := fun v => Q v n) (by omega) hQ
  -- the lower bound `g(u_n) - 1/(u_n + 1) ≤ a_{u_n}(n)` and the squeeze
  have hlow : ∀ n, g (u n) - 1 / ((u n : ℝ) + 1) ≤ a (u n) n := fun n =>
    (hspec n).2 n le_rfl (u n) le_rfl
  have hg' : Tendsto (fun n => g (u n) - 1 / ((u n : ℝ) + 1)) atTop (nhds 1) := by
    have h1 : Tendsto (fun n => g (u n)) atTop (nhds 1) := hg.comp hu
    have h2 : Tendsto (fun n => 1 / ((u n : ℝ) + 1)) atTop (nhds 0) :=
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hu
    simpa using h1.sub h2
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hg' tendsto_const_nhds hlow fun n => ha1 _ _

/-- eq. (1) with `u_n ≤ n/4` from the uniqueness of the infinite cluster. [cite:
 DuminilCopinSidoraviciusTassion2016, §2.1 (eq. (1))]
-/
theorem DuminilCopinSidoraviciusTassion2016_eq1'_of_uniqueCluster
    (hU : DuminilCopinSidoraviciusTassion2016_uniqueCluster) :
    DuminilCopinSidoraviciusTassion2016_eq1' := by
  intro k hk p hθ
  exact exists_seq_tendsto_one_of_liminf4
    (a := fun v n => (bondPercolation (slabGraph 3 k) p).real
      (slabUniqueConn k (sqBox 0 n) (sqBox 0 v) (sqSphere 0 n)))
    (g := fun v => (bondPercolation (slabGraph 3 k) p).real (boxToInfinity k v))
    (fun v n => measureReal_nonneg) (fun v n => measureReal_le_one) (fun v => measureReal_le_one)
    (fun v ε hε => le_eventually_real_slabUniqueConn k (hU k hk p hθ) v hε)
    (tendsto_real_boxToInfinity k hθ)

/-! ## eq. (12) from Lemma 4 and Lemma 6' ; eq. (13); the finite-size criterion -/

/-- [cite: DuminilCopinSidoraviciusTassion2016, §2.1 eqs. (10)–(12)] -/
theorem DuminilCopinSidoraviciusTassion2016_eq12'_of_lemmas (h4 : DuminilCopinSidoraviciusTassion2016_lemma4)
    (h6 : DuminilCopinSidoraviciusTassion2016_lemma6') : DuminilCopinSidoraviciusTassion2016_eq12' := by
  intro k hk p hθ u hu4 hlim
  have hu3 : ∀ n, 3 * u n ≤ n := fun n => by have := hu4 n; omega
  obtain ⟨α, a, b, hαab, hev, hT1, hT2⟩ := h4 k hk p hθ u hu3 hlim
  set P := bondPercolation (slabGraph 3 k) p with hP
  -- `y_m := ⌊(a_m + b_m)/2⌋`
  refine ⟨fun m => (((a m + b m) / 2 : ℕ) : ℤ), ?_, ?_⟩
  · intro m hm
    obtain ⟨-, hαm, hab, hbα, -⟩ := hαab m hm
    refine ⟨by positivity, ?_⟩
    show ((((a m + b m) / 2 : ℕ)) : ℤ) ≤ m
    have : (a m + b m) / 2 ≤ m := by omega
    exact_mod_cast this
  intro ε hε N
  -- Lemma 6 with `ε/2`
  obtain ⟨δ, hδ, h6'⟩ := h6 k hk p hθ (ε / 2) (by positivity)
  -- trivial when `δ > 3`? no: we make the three factors `> 1 - δ/3`
  have hδ3 : 0 < δ / 3 := by positivity
  have hev1 : ∀ᶠ m in atTop, P.real (sideEvent k m (u m) (α m) m) ∈ Set.Ioi (1 - δ / 3) :=
    hT1.eventually (Ioi_mem_nhds (show (1 : ℝ) - δ / 3 < 1 by linarith))
  have hev2 : ∀ᶠ m in atTop, P.real (sideEvent k m (u m) (a m) (b m)) ∈ Set.Ioi (1 - δ / 3) :=
    hT2.eventually (Ioi_mem_nhds (show (1 : ℝ) - δ / 3 < 1 by linarith))
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.1 (hev1.and (hev2.and hev))
  -- Lemma 5: a scale `n ≥ max (max N M) 2` with `α_{3n} ≤ 4 α_n`
  obtain ⟨n, hn, hn1, hL5⟩ := DuminilCopinSidoraviciusTassion2016_lemma5 α (fun n hn => (hαab n hn).1)
    (fun n hn => (hαab n hn).2.1) (max (max N M) 4)
  have hNn : N ≤ n := ((le_max_left _ _).trans (le_max_left _ _)).trans hn
  have hMn : M ≤ n := ((le_max_right _ _).trans (le_max_left _ _)).trans hn
  have hn4 : 4 ≤ n := (le_max_right _ _).trans hn
  have hn2 : 2 ≤ n := by omega
  refine ⟨n, hNn, ?_⟩
  obtain ⟨hMn1, hMn2, hαn1⟩ := hM n hMn
  obtain ⟨-, hM3n2, -⟩ := hM (3 * n) (by omega)
  obtain ⟨hα1, hαn, habn, hbαn, hlen⟩ := hαab n (by omega)
  obtain ⟨hα13, hα3n, hab3, hbα3, hlen3⟩ := hαab (3 * n) (by omega)
  have hun : u n ≤ n := by have := hu3 n; omega
  have hu3n : u (3 * n) + 1 ≤ n := by have := hu4 (3 * n); omega
  -- the data at scale `n`
  set y : ℤ := (((a (3 * n) + b (3 * n)) / 2 : ℕ) : ℤ) with hy
  have hy0 : 0 ≤ y := by positivity
  have hyb : y ≤ b (3 * n) := by
    have : (a (3 * n) + b (3 * n)) / 2 ≤ b (3 * n) := by omega
    rw [hy]
    exact_mod_cast this
  have hya : (a (3 * n) : ℤ) ≤ y := by
    have : a (3 * n) ≤ (a (3 * n) + b (3 * n)) / 2 := by omega
    rw [hy]
    exact_mod_cast this
  have hy3n : y ≤ 3 * n := by
    have : b (3 * n) ≤ 3 * n := hbα3.trans hα3n
    have : (b (3 * n) : ℤ) ≤ 3 * (n : ℤ) := by exact_mod_cast this
    linarith
  -- (10): `E_{3n}(a_{3n}, b_{3n}) ⊆ {S_{3n} ⟷^{B_{3n}} Z_n}`
  set Zev := slabConn k (sqBox 0 (3 * n)) (sqBox 0 (u (3 * n)))
    (sideSeg (3 * n) (y - α n) (y + α n)) with hZev
  have h10 : sideEvent k (3 * n) (u (3 * n)) (a (3 * n)) (b (3 * n)) ⊆ Zev := by
    refine openCrossing_mono subset_rfl subset_rfl (slabLift_mono k ?_)
    push_cast
    refine sideSeg_mono _ ?_ ?_
    · -- `y - α_n ≤ a_{3n}`
      have hq : (a (3 * n) + b (3 * n)) / 2 ≤ a (3 * n) + α n := by omega
      have hq' : (((a (3 * n) + b (3 * n)) / 2 : ℕ) : ℤ) ≤ (a (3 * n) : ℤ) + (α n : ℤ) := by
        exact_mod_cast hq
      rw [hy]
      linarith
    · -- `b_{3n} ≤ y + α_n`
      have hq : b (3 * n) ≤ (a (3 * n) + b (3 * n)) / 2 + α n := by omega
      have hq' : (b (3 * n) : ℤ) ≤ (((a (3 * n) + b (3 * n)) / 2 : ℕ) : ℤ) + (α n : ℤ) := by
        exact_mod_cast hq
      rw [hy]
      linarith
  have hZval : 1 - δ / 3 < P.real Zev :=
    lt_of_lt_of_le hM3n2 (measureReal_mono h10)
  -- (11): Harris twice, and the symmetric copies of `E_n(α_n, n)`
  set Bp := sqBox (2 * (n : ℤ), y) n with hBp
  set Sp := sqBox (2 * (n : ℤ), y) (u n) with hSp
  set Ym := slabConn k Bp Sp (sideSeg (3 * n) (y - n) (y - α n)) with hYm
  set Yp := slabConn k Bp Sp (sideSeg (3 * n) (y + α n) (y + n)) with hYp
  obtain ⟨hYpval, hYmval⟩ := real_sideEvent_translate k p n (u n) (α n) y
  have hZm : MeasurableSet Zev := measurableSet_slabConn k 0 (3 * n) _ _
  have hYmm : MeasurableSet Ym := measurableSet_slabConn k _ n _ _
  have hYpm : MeasurableSet Yp := measurableSet_slabConn k _ n _ _
  have hH1 : P.real Zev * P.real Ym ≤ P.real (Zev ∩ Ym) :=
    harris_fkg_holds (slabGraph 3 k) p (isUpperSet_openCrossing _ _ _)
      (isUpperSet_openCrossing _ _ _) hZm hYmm
  have hH2 : P.real (Zev ∩ Ym) * P.real Yp ≤ P.real (Zev ∩ Ym ∩ Yp) :=
    harris_fkg_holds (slabGraph 3 k) p ((isUpperSet_openCrossing _ _ _).inter
      (isUpperSet_openCrossing _ _ _)) (isUpperSet_openCrossing _ _ _) (hZm.inter hYmm) hYpm
  have hYm' : 1 - δ / 3 < P.real Ym := by rw [hYm, hBp, hSp, hP, hYmval]; exact hMn1
  have hYp' : 1 - δ / 3 < P.real Yp := by rw [hYp, hBp, hSp, hP, hYpval]; exact hMn1
  have htriple : 1 - δ ≤ P.real (Zev ∩ Ym ∩ Yp) := by
    rcases lt_or_ge 3 δ with hδ3' | hδ3'
    · have : 0 ≤ P.real (Zev ∩ Ym ∩ Yp) := measureReal_nonneg
      linarith
    · have h0 : 0 ≤ 1 - δ / 3 := by linarith
      have h1 : (1 - δ / 3) * (1 - δ / 3) ≤ P.real Zev * P.real Ym :=
        mul_le_mul hZval.le hYm'.le h0 (h0.trans hZval.le)
      have h2 : (1 - δ / 3) * (1 - δ / 3) * (1 - δ / 3) ≤ P.real (Zev ∩ Ym) * P.real Yp :=
        mul_le_mul (h1.trans hH1) hYp'.le h0 measureReal_nonneg
      have hx1 : δ / 3 ≤ 1 := by linarith
      have hcube : 1 - δ ≤ (1 - δ / 3) * (1 - δ / 3) * (1 - δ / 3) := by
        nlinarith [sq_nonneg (δ / 3), mul_nonneg (mul_nonneg hδ3.le hδ3.le) (sub_nonneg.2 hx1)]
      linarith [hH2, h2, hcube]
  -- Lemma 6
  have h6n := h6' n (u (3 * n)) (u n) (α n) y hn2 hu3n (hu3 n) hα1 hαn1 hy0 hy3n htriple
  -- `B_{3n} ∪ B'_n ⊆ B_{4n}`
  have hmono : slabConn k (sqBox 0 (3 * n) ∪ Bp) (sqBox 0 (u (3 * n))) Sp ⊆
      slabConn k (sqBox 0 (4 * n)) (sqBox 0 (u (3 * n))) Sp := by
    refine openCrossing_mono (slabLift_mono k ?_) subset_rfl subset_rfl
    rintro w (hw | hw)
    · exact sqBox_mono 0 (by omega) hw
    · simp only [hBp, sqBox, Set.mem_setOf_eq, abs_le, Prod.fst_zero, Prod.snd_zero,
        sub_zero] at hw ⊢
      omega
  have hfin := measureReal_mono (μ := P) hmono
  show 1 - ε < P.real (slabConn k (sqBox 0 (4 * n)) (sqBox 0 (u (3 * n))) (sqBox (2 * (n : ℤ), y) (u n)))
  simp only [hBp, hSp] at hfin
  rw [hP] at hfin ⊢
  linarith

/-- **eq. (13) from eq. (12) and eq. (1)** for sequences with `u_n ≤ n/4`. [cite:
 DuminilCopinSidoraviciusTassion2016, §2.1 eq. (13) (proof)]
-/
theorem DuminilCopinSidoraviciusTassion2016_eq13'_of_eq12' (h12 : DuminilCopinSidoraviciusTassion2016_eq12') :
    DuminilCopinSidoraviciusTassion2016_eq13' := by
  intro k hk p hθ u hu4 hlim ε hε N
  obtain ⟨y, hy, h12'⟩ := h12 k hk p hθ u hu4 hlim
  set P := bondPercolation (slabGraph 3 k) p with hP
  -- trivial when `ε > 3`
  rcases lt_or_ge 3 ε with hε3 | hε3
  · refine ⟨N, le_rfl, ?_⟩
    have : 0 ≤ P.real (slabConn k (sqBox (2 * (N : ℤ), 0) (6 * N)) (sqBox 0 (u (3 * N)))
      (sqBox (4 * (N : ℤ), 0) (u (3 * N)))) := measureReal_nonneg
    linarith
  have hε3' : 0 < ε / 3 := by positivity
  -- eq. (1): eventually the uniqueness event has probability `> 1 - ε/3`
  have hev : ∀ᶠ m in atTop, P.real (slabUniqueConn k (sqBox 0 m) (sqBox 0 (u m)) (sqSphere 0 m))
      ∈ Set.Ioi (1 - ε / 3) :=
    hlim.eventually (Ioi_mem_nhds (show (1 : ℝ) - ε / 3 < 1 by linarith))
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.1 hev
  -- eq. (12) at a scale `n ≥ max (max N N₁) 1`
  obtain ⟨n, hn, h12n⟩ := h12' (ε / 3) hε3' (max (max N N₁) 1)
  have hNn : N ≤ n := ((le_max_left _ _).trans (le_max_left _ _)).trans hn
  have hN₁n : N₁ ≤ n := ((le_max_right _ _).trans (le_max_left _ _)).trans hn
  have hn1 : 1 ≤ n := (le_max_right _ _).trans hn
  refine ⟨n, hNn, ?_⟩
  obtain ⟨hy0, hyn⟩ := hy (3 * n) (by omega)
  have hun : u n ≤ n := by have := hu4 n; omega
  have hu3n : u (3 * n) ≤ n := by have := hu4 (3 * n); omega
  -- the events
  set c : ℤ × ℤ := (2 * (n : ℤ), y (3 * n)) with hc
  set E := slabConn k (sqBox 0 (4 * n)) (sqBox 0 (u (3 * n))) (sqBox c (u n)) with hE
  set E' := slabConn k (sqBox (4 * (n : ℤ), 0) (4 * n)) (sqBox (4 * (n : ℤ), 0) (u (3 * n)))
    (sqBox c (u n)) with hE'
  set U' := slabUniqueConn k (sqBox c n) (sqBox c (u n)) (sqSphere c n) with hU'
  have hEval : 1 - ε / 3 < P.real E := h12n
  -- reflection: `P[E'] = P[E]`
  have hE'val : P.real E' = P.real E := by
    have himg : E' = slabConn k (planarReflect (4 * n) '' sqBox 0 (4 * n))
        (planarReflect (4 * n) '' sqBox 0 (u (3 * n))) (planarReflect (4 * n) '' sqBox c (u n)) := by
      rw [image_planarReflect_sqBox, image_planarReflect_sqBox, image_planarReflect_sqBox]
      have h1 : ((4 * (n : ℤ)) - (0 : ℤ × ℤ).1, (0 : ℤ × ℤ).2) = ((4 * (n : ℤ)), (0 : ℤ)) := by simp
      have h2 : ((4 * (n : ℤ)) - c.1, c.2) = c := by
        simp only [hc, Prod.mk.injEq, and_true]; ring
      rw [h1, h2]
    have hpre : slabRelabel k (planarReflect (4 * n)) ⁻¹' E' = E := by
      rw [himg]
      exact preimage_slabRelabel_slabConn k _ _ _ _
    rw [← hpre, hP, real_preimage_slabRelabel k _ (planarAdj_planarReflect (4 * n))]
  -- Harris: `P[E ∩ E'] ≥ P[E]²`
  have hEup : IsUpperSet E := isUpperSet_openCrossing _ _ _
  have hE'up : IsUpperSet E' := isUpperSet_openCrossing _ _ _
  have hEm : MeasurableSet E := measurableSet_slabConn k 0 (4 * n) _ _
  have hE'm : MeasurableSet E' := measurableSet_slabConn k _ (4 * n) _ _
  have hHarris : P.real E * P.real E' ≤ P.real (E ∩ E') :=
    harris_fkg_holds (slabGraph 3 k) p hEup hE'up hEm hE'm
  -- translation: `P[U'] = P[U_n] > 1 - ε/3`
  have hU'val : 1 - ε / 3 < P.real U' := by
    rw [hU', hP, real_slabUniqueConn_shift]
    exact hN₁ n hN₁n
  -- union bound and gluing
  have hU'm : MeasurableSet U' := measurableSet_slabUniqueConn k c n _ _
  have hunion := measureReal_inter_ge P (E ∩ E') hU'm
  have hglue : P.real (E ∩ E' ∩ U') ≤ P.real (slabConn k (sqBox (2 * (n : ℤ), 0) (6 * n))
      (sqBox 0 (u (3 * n))) (sqBox (4 * (n : ℤ), 0) (u (3 * n)))) := by
    refine real_glue_le k p ?_ ?_ ?_ ?_ ?_ ?_
    · -- `B_{4n} ⊆ (2n,0) + B_{6n}`
      intro w hw
      simp only [sqBox, Set.mem_setOf_eq, abs_le, Prod.fst_zero, Prod.snd_zero, sub_zero] at hw ⊢
      omega
    · -- `(4n,0) + B_{4n} ⊆ (2n,0) + B_{6n}`
      intro w hw
      simp only [sqBox, Set.mem_setOf_eq, abs_le, sub_zero] at hw ⊢
      omega
    · -- `B'_n ⊆ B_{4n}`
      intro w hw
      simp only [sqBox, Set.mem_setOf_eq, abs_le, hc, Prod.fst_zero, Prod.snd_zero, sub_zero] at hw ⊢
      omega
    · exact sqBox_mono c hun
    · -- `S_{3n}` meets `B'_n` only on its boundary
      rintro w ⟨hw1, hw2⟩
      rw [mem_sqSphere_iff]
      refine ⟨hw2, Or.inl ?_⟩
      rw [le_abs, hc]
      simp only [sqBox, Set.mem_setOf_eq, abs_le, hc, Prod.fst_zero, Prod.snd_zero,
        sub_zero] at hw1 hw2
      dsimp only
      omega
    · rintro w ⟨hw1, hw2⟩
      rw [mem_sqSphere_iff]
      refine ⟨hw2, Or.inl ?_⟩
      rw [le_abs, hc]
      simp only [sqBox, Set.mem_setOf_eq, abs_le, hc] at hw1 hw2
      dsimp only at hw1 hw2 ⊢
      omega
  -- numerics: `P[E]² + P[U'] - 1 > 1 - ε`
  have hE1 : P.real E ≤ 1 := measureReal_le_one
  have hsq : (1 - ε / 3) * (1 - ε / 3) ≤ P.real E * P.real E' := by
    rw [hE'val]
    have h0 : 0 ≤ 1 - ε / 3 := by linarith
    exact mul_le_mul hEval.le hEval.le h0 (h0.trans hEval.le)
  nlinarith [hHarris, hunion, hglue, hU'val, hsq]

/-- **the finite-size criterion from eq. (1') and eq. (13')**. [cite:
 DuminilCopinSidoraviciusTassion2016, §2.2 (p. 6)]
-/
theorem DuminilCopinSidoraviciusTassion2016_goodEvent_likely_of_eq1'_eq13' (h1 : DuminilCopinSidoraviciusTassion2016_eq1')
    (h13 : DuminilCopinSidoraviciusTassion2016_eq13') :
    DuminilCopinSidoraviciusTassion2016_goodEvent_likely := by
  intro k hk p hθ η hη
  obtain ⟨u, hu4, hlim⟩ := h1 k hk p hθ
  set P := bondPercolation (slabGraph 3 k) p with hP
  have hη3 : 0 < η / 3 := by positivity
  -- eq. (1): eventually the uniqueness event has probability `> 1 - η/3`
  have hev : ∀ᶠ m in atTop, P.real (slabUniqueConn k (sqBox 0 m) (sqBox 0 (u m)) (sqSphere 0 m))
      ∈ Set.Ioi (1 - η / 3) :=
    hlim.eventually (Ioi_mem_nhds (show (1 : ℝ) - η / 3 < 1 by linarith))
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.1 hev
  -- eq. (13): a scale `n ≥ max N₁ 1` at which the two-block connection is likely
  obtain ⟨n, hn, h13n⟩ := h13 k hk p hθ u hu4 hlim (η / 3) hη3 (max N₁ 1)
  have hn1 : 1 ≤ n := (le_max_right _ _).trans hn
  have hN₁n : N₁ ≤ 3 * n := ((le_max_left _ _).trans hn).trans (by omega)
  refine ⟨n, u (3 * n), hn1, by have := hu4 (3 * n); omega, ?_⟩
  -- the three constituents of `good(n, u_{3n}, 0, e₀)`
  have hii₀ : 1 - η / 3 <
      P.real (slabUniqueConn k (sqBox 0 (3 * n)) (sqBox 0 (u (3 * n))) (sqSphere 0 (3 * n))) :=
    hN₁ (3 * n) hN₁n
  have hii₁ : 1 - η / 3 < P.real (slabUniqueConn k (sqBox (0 + coarseShift (4 * n) 0) (3 * n))
      (sqBox (0 + coarseShift (4 * n) 0) (u (3 * n))) (sqSphere (0 + coarseShift (4 * n) 0) (3 * n))) := by
    rw [hP, real_slabUniqueConn_shift]
    exact hii₀
  have hi : 1 - η / 3 < P.real (slabConn k (sqBox (0 + coarseShift (2 * n) 0) (6 * n))
      (sqBox 0 (u (3 * n))) (sqBox (0 + coarseShift (4 * n) 0) (u (3 * n)))) := by
    have e1 : (0 : ℤ × ℤ) + coarseShift (2 * n) 0 = (2 * (n : ℤ), 0) := by simp [coarseShift]
    have e2 : (0 : ℤ × ℤ) + coarseShift (4 * n) 0 = (4 * (n : ℤ), 0) := by simp [coarseShift]
    rw [e1, e2]
    exact h13n
  -- union bound
  have hgood₀ : 1 - η < P.real (goodEvent k n (u (3 * n)) 0 0) := by
    have hBC := measureReal_inter_ge P
      (slabUniqueConn k (sqBox 0 (3 * n)) (sqBox 0 (u (3 * n))) (sqSphere 0 (3 * n)))
      (measurableSet_slabUniqueConn k (0 + coarseShift (4 * n) 0) (3 * n)
        (sqBox (0 + coarseShift (4 * n) 0) (u (3 * n))) (sqSphere (0 + coarseShift (4 * n) 0) (3 * n)))
    have hABC := measureReal_inter_ge P
      (slabConn k (sqBox (0 + coarseShift (2 * n) 0) (6 * n)) (sqBox 0 (u (3 * n)))
        (sqBox (0 + coarseShift (4 * n) 0) (u (3 * n))))
      ((measurableSet_slabUniqueConn k 0 (3 * n) (sqBox 0 (u (3 * n))) (sqSphere 0 (3 * n))).inter
        (measurableSet_slabUniqueConn k (0 + coarseShift (4 * n) 0) (3 * n)
          (sqBox (0 + coarseShift (4 * n) 0) (u (3 * n)))
          (sqSphere (0 + coarseShift (4 * n) 0) (3 * n))))
    unfold goodEvent
    linarith
  intro i
  fin_cases i
  · exact hgood₀
  · show 1 - η < P.real (goodEvent k n (u (3 * n)) 0 1)
    rw [hP, real_goodEvent_one_eq]
    exact hgood₀

/-- **DST 2016, Thm. 1 from the Gluing Lemma in the range `u_{3n} + 1 ≤ n`**: with
uniqueness (`SlabUniqueness.lean`), the renormalisation step and dependent percolation
(`SlabCriticalityInputs.lean`), Lemmata 4–5 and eqs. (10)–(13) (`SlabCriticality.lean`, here in
the `u_n ≤ n/4` form), the named fact `DuminilCopinSidoraviciusTassion2016` follows from
`DuminilCopinSidoraviciusTassion2016_lemma6'`. [cite: DuminilCopinSidoraviciusTassion2016, Thm. 1 and Lemma 6] -/
theorem DuminilCopinSidoraviciusTassion2016.of_lemma6' (h6 : DuminilCopinSidoraviciusTassion2016_lemma6') :
    DuminilCopinSidoraviciusTassion2016 :=
  DuminilCopinSidoraviciusTassion2016.of_criterion
    (DuminilCopinSidoraviciusTassion2016_goodEvent_likely_of_eq1'_eq13'
      (DuminilCopinSidoraviciusTassion2016_eq1'_of_uniqueCluster
        DuminilCopinSidoraviciusTassion2016_uniqueCluster_holds)
      (DuminilCopinSidoraviciusTassion2016_eq13'_of_eq12'
        (DuminilCopinSidoraviciusTassion2016_eq12'_of_lemmas DuminilCopinSidoraviciusTassion2016_lemma4_holds h6)))
    DuminilCopinSidoraviciusTassion2016_renormalisation_holds

end Percolation.Literature

end
