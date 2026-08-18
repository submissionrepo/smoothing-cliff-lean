/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Optimization.DynamicProgramming.Budget.StochasticBudgetDP

/-!
# Endogenous-default / option-value dynamic programing

An **option-value** Bellman operator on top of the generic stochastic budget DP
(`StochBudgetData`). At each state the household chooses the better of two values: A *keep*
objective `M.bellmanOp v` (the recursive continuation of `M`) and a fixed *outside option* `vOut`.
The headline object is the value

`V(st) = max ( (M.bellmanOp V)(st) , vOut(st) )`,

the unique uniformly bounded fixed point of the operator `v ↦ max (M.bellmanOp v) vOut`. This is
the endogenous-default / foreclosure value `V^H = max(V_keep, V_fc)`: The keep branch recurses
through `M`, while the outside-option branch `vOut` is an absorbing alternative (e.g. the renter
value net of the foreclosure costs `F, Ξ` — a value that does **not** depend on `V^H`, so it is
solved first and passed in as data).

Because the value is a pointwise maximum of two functions, it need not be globally concave — at a
crossing with unequal branch slopes it has a **convex kink**, so the smooth Benveniste–Scheinkman
envelope does not apply there. This file therefore provides the kink-aware machinery: One-sided
derivatives of the max (whose right/left values are `max`/`min` of the branch derivatives, i.e. the
endpoints of the **convex hull of the two branch gradients** — the Clarke generalized gradient at
the kink, which the foreclosure spec loosely calls the "superdifferential"), and the
interior-region envelope (`V` agrees with the dominant branch off the switching locus).

## Main definitions

* `StochBudgetData.optionBellmanOp` — the operator `v ↦ max (M.bellmanOp v) vOut`
* `StochBudgetData.optionValueFunction` — its unique uniformly bounded fixed point `V`
* `StochBudgetData.defaultSet` — the states where the outside option weakly dominates the keep value

## Main statements

* `StochBudgetData.optionValueFunction_eq_max` — the Bellman equation `V = max (M.bellmanOp V) vOut`
* `StochBudgetData.existsUnique_bdd_optionFixedPoint` — existence/uniqueness of the bounded fixed
  point
* `fixedPoint_le_of_operator_le` — monotone comparative statics of bounded fixed points: An ordered
  pair of monotone-discounting operators has ordered fixed points
* `StochBudgetData.optionValueFunction_mono_of_bellmanOp_le` — `V` is monotone in a keep-side
  parameter that enlarges the keep value, hence (`defaultSet_antitone_keep`) the default set is
  antitone in that parameter
* `StochBudgetData.optionValueFunction_concaveOn_of_keep_dominant` /
  `optionValueFunction_concaveOn_of_vOut_dominant` — branchwise concavity: `V` is concave on a
  convex region where one (concave) branch dominates
* `hasDerivWithinAt_max_Ici` / `hasDerivWithinAt_max_Iic` — the one-sided derivatives of a max at a
  tie point are `max` / `min` of the branch derivatives (the endpoints of the convex hull of the
  two branch gradients)
* `hasDerivAt_max_of_lt` — interior-region envelope: Off the switching locus, `max f g` is
  differentiable with the dominant branch's derivative

## Tags

dynamic programing, option value, endogenous default, foreclosure, kink, generalized gradient,
piecewise concave, comparative statics
-/

@[expose] public section

namespace Econlib.Optimization.DynamicProgramming

open Blackwell Filter Topology Set

/-! ### The option-value operator and its bounded fixed point

The operator `v ↦ max (M.bellmanOp v) vOut` is built from the keep operator `M.bellmanOp` and a
fixed bounded outside option `vOut`. Because `|max a c − max b c| ≤ |a − b|`, taking the max with a
fixed function preserves Blackwell's monotonicity and discounting conditions, so the
Banach/Blackwell fixed-point theory carries over verbatim from `StochBudgetData`.

**Inherited zero convention.** Where the keep budget is empty `M.bellmanOp v` is `sSup ∅ = 0` (the
`StochBudgetData` convention), so on that region `optionBellmanOp` reads `max 0 vOut`. This only
matters off the economically interpreted domain: Keep budgets are nonempty for net worth `w > 0`
(income is positive), so the zero is never a phantom keep payoff there. Downstream consumers state
their comparative statics on `0 < w`. -/

namespace StochBudgetData

variable {n : ℕ} {A : Type*} (M : StochBudgetData n A) (vOut : ℝ × Fin n → ℝ)

/-- The **option-value Bellman operator**: At each state the household takes the better of the keep
objective `M.bellmanOp v` and the fixed outside option `vOut`. Its fixed point is the option value
`V^H = max(V_keep, V_fc)`. -/
noncomputable def optionBellmanOp (v : ℝ × Fin n → ℝ) (st : ℝ × Fin n) : ℝ :=
  max (M.bellmanOp v st) (vOut st)

@[simp] lemma optionBellmanOp_eq_max (v : ℝ × Fin n → ℝ) (st : ℝ × Fin n) :
    M.optionBellmanOp vOut v st = max (M.bellmanOp v st) (vOut st) := rfl

/-- **`optionBellmanOp` maps bounded functions to bounded functions.** The max of two bounded
functions is bounded. -/
lemma optionBellmanOp_bounded [NeZero n] [Nonempty A] {Br : ℝ} (hBr : ∀ a, |M.reward a| ≤ Br)
    (hOut : UniformBounded vOut) (v : ℝ × Fin n → ℝ) (hv : UniformBounded v) :
    UniformBounded (M.optionBellmanOp vOut v) := by
  obtain ⟨B₁, hB₁⟩ := M.bellmanOp_bounded hBr v hv
  obtain ⟨B₂, hB₂⟩ := hOut
  refine ⟨max B₁ B₂, fun st => ?_⟩
  rw [optionBellmanOp_eq_max, abs_le]
  obtain ⟨hlo₁, hhi₁⟩ := abs_le.mp (hB₁ st)
  obtain ⟨hlo₂, hhi₂⟩ := abs_le.mp (hB₂ st)
  refine ⟨le_max_of_le_left ((neg_le_neg (le_max_left B₁ B₂)).trans hlo₁), ?_⟩
  exact max_le (hhi₁.trans (le_max_left _ _)) (hhi₂.trans (le_max_right _ _))

/-- **Monotonicity (Blackwell condition 1)** for the option operator. -/
lemma optionBellmanOp_monotone {Br : ℝ} (hBr : ∀ a, |M.reward a| ≤ Br)
    (v w : ℝ × Fin n → ℝ) (hw : UniformBounded w) (hvw : ∀ p, v p ≤ w p) :
    ∀ st, M.optionBellmanOp vOut v st ≤ M.optionBellmanOp vOut w st := fun st =>
  max_le_max (M.bellmanOp_monotone hBr v w hw hvw st) le_rfl

/-- **Discounting (Blackwell condition 2)** for the option operator. The outside option absorbs the
shift `≤ vOut + βc` since `βc ≥ 0`, and the keep branch inherits the keep operator's discounting. -/
lemma optionBellmanOp_discounting {Br : ℝ} (hBr : ∀ a, |M.reward a| ≤ Br)
    (v : ℝ × Fin n → ℝ) (c : ℝ) (hv : UniformBounded v) (hc : 0 ≤ c) :
    ∀ st, M.optionBellmanOp vOut (fun p => v p + c) st ≤ M.optionBellmanOp vOut v st + M.β * c := by
  intro st
  have hkeep := M.bellmanOp_discounting hBr v c hv hc st
  have hβc : 0 ≤ M.β * c := mul_nonneg M.β_nonneg hc
  rw [optionBellmanOp_eq_max, optionBellmanOp_eq_max]
  refine max_le ?_ ?_
  · calc M.bellmanOp (fun p => v p + c) st
        ≤ M.bellmanOp v st + M.β * c := hkeep
      _ ≤ max (M.bellmanOp v st) (vOut st) + M.β * c := by gcongr; exact le_max_left _ _
  · calc vOut st ≤ max (M.bellmanOp v st) (vOut st) := le_max_right _ _
      _ ≤ max (M.bellmanOp v st) (vOut st) + M.β * c := by linarith

/-- The sup-norm contraction estimate for the option operator. -/
lemma optionBellmanOp_apply_abs_sub_le {Br : ℝ}
    (hBr : ∀ a, |M.reward a| ≤ Br)
    (v w : ℝ × Fin n → ℝ) (hv : UniformBounded v) (hw : UniformBounded w) (st : ℝ × Fin n) :
    |M.optionBellmanOp vOut v st - M.optionBellmanOp vOut w st| ≤ M.β * ⨆ t, |v t - w t| :=
  Blackwell.abs_sub_le_of_monotone_discounting
    (fun a b _ hb hab => M.optionBellmanOp_monotone vOut hBr a b hb hab)
    (fun a c hb hc => M.optionBellmanOp_discounting vOut hBr a c hb hc) hv hw st

/-- The lifted option operator is a Banach contraction with modulus `β`. -/
lemma contractingWith_liftOptionBellmanOp [NeZero n] [Nonempty A] {Br : ℝ}
    (hBr : ∀ a, |M.reward a| ≤ Br) (hOut : UniformBounded vOut) :
    ContractingWith ⟨M.β, M.β_nonneg⟩
      (Blackwell.liftBddFun (M.optionBellmanOp vOut)
        (fun v hv => M.optionBellmanOp_bounded vOut hBr hOut v hv)) :=
  Blackwell.contractingWith_liftBddFun M.β_nonneg M.β_lt_one
    (M.optionBellmanOp_apply_abs_sub_le vOut hBr)

/-- The **option value function** `V^H`: The unique uniformly bounded fixed point of the option
operator `v ↦ max (M.bellmanOp v) vOut`. -/
noncomputable def optionValueFunction [NeZero n] [Nonempty A] {Br : ℝ}
    (hBr : ∀ a, |M.reward a| ≤ Br) (hOut : UniformBounded vOut) : ℝ × Fin n → ℝ :=
  Blackwell.bddFixedPoint (M.contractingWith_liftOptionBellmanOp vOut hBr hOut)

/-- The option value function is uniformly bounded. -/
theorem optionValueFunction_bounded [NeZero n] [Nonempty A] {Br : ℝ}
    (hBr : ∀ a, |M.reward a| ≤ Br) (hOut : UniformBounded vOut) :
    UniformBounded (M.optionValueFunction vOut hBr hOut) :=
  Blackwell.bddFixedPoint_bounded _

/-- The option value function satisfies the option Bellman equation pointwise. -/
theorem optionValueFunction_isFixedPt [NeZero n] [Nonempty A] {Br : ℝ}
    (hBr : ∀ a, |M.reward a| ≤ Br) (hOut : UniformBounded vOut) (st : ℝ × Fin n) :
    M.optionValueFunction vOut hBr hOut st =
      M.optionBellmanOp vOut (M.optionValueFunction vOut hBr hOut) st :=
  Blackwell.bddFixedPoint_isFixedPt _ st

/-- **The option Bellman equation:** `V(st) = max ( (M.bellmanOp V)(st) , vOut(st) )`. -/
theorem optionValueFunction_eq_max [NeZero n] [Nonempty A] {Br : ℝ}
    (hBr : ∀ a, |M.reward a| ≤ Br) (hOut : UniformBounded vOut) (st : ℝ × Fin n) :
    M.optionValueFunction vOut hBr hOut st =
      max (M.bellmanOp (M.optionValueFunction vOut hBr hOut) st) (vOut st) :=
  M.optionValueFunction_isFixedPt vOut hBr hOut st

/-- The outside option is dominated by the option value: `vOut ≤ V`. -/
lemma vOut_le_optionValueFunction [NeZero n] [Nonempty A] {Br : ℝ}
    (hBr : ∀ a, |M.reward a| ≤ Br) (hOut : UniformBounded vOut) (st : ℝ × Fin n) :
    vOut st ≤ M.optionValueFunction vOut hBr hOut st := by
  rw [M.optionValueFunction_eq_max vOut hBr hOut st]; exact le_max_right _ _

/-- The keep branch is dominated by the option value: `M.bellmanOp V ≤ V`. -/
lemma bellmanOp_optionValueFunction_le [NeZero n] [Nonempty A] {Br : ℝ}
    (hBr : ∀ a, |M.reward a| ≤ Br) (hOut : UniformBounded vOut) (st : ℝ × Fin n) :
    M.bellmanOp (M.optionValueFunction vOut hBr hOut) st ≤
      M.optionValueFunction vOut hBr hOut st := by
  rw [M.optionValueFunction_eq_max vOut hBr hOut st]; exact le_max_left _ _

/-- **Existence and uniqueness** of the uniformly bounded option value function. -/
theorem existsUnique_bdd_optionFixedPoint [NeZero n] [Nonempty A] {Br : ℝ}
    (hBr : ∀ a, |M.reward a| ≤ Br) (hOut : UniformBounded vOut) :
    ∃! v : (ℝ × Fin n) → ℝ,
      UniformBounded v ∧ ∀ st, v st = M.optionBellmanOp vOut v st :=
  Blackwell.existsUnique_bdd_fixedPoint (M.contractingWith_liftOptionBellmanOp vOut hBr hOut)

end StochBudgetData

/-! ### Monotone comparative statics of bounded fixed points

A keep-side parameter that enlarges the keep value raises the whole option value, which (below)
shrinks the default set. The engine is an order-comparison of two bounded fixed points that needs
only one discounting step — no iteration. -/

/-- **Monotone comparative statics of bounded fixed points.** If `T₂` is monotone and satisfies the
discounting property with factor `β < 1`, and `V₁`, `V₂` are uniformly bounded fixed points of
`T₁`, `T₂` with `T₁ V₁ ≤ T₂ V₁` pointwise, then `V₁ ≤ V₂` pointwise.

Only the *larger* operator `T₂` need be monotone and discounting, and the operator order is
required only at the fixed point `V₁`. The proof bounds `c := ⨆ (V₁ − V₂)` above by `β · c⁺`
through a single discounting step, which forces `c ≤ 0`. -/
theorem fixedPoint_le_of_operator_le {S : Type*} [Nonempty S]
    {T₁ T₂ : (S → ℝ) → S → ℝ} {β : ℝ} (hβ₁ : β < 1)
    (h_mono₂ : ∀ v w : S → ℝ, UniformBounded v → UniformBounded w → (∀ s, v s ≤ w s) →
      ∀ s, T₂ v s ≤ T₂ w s)
    (h_disc₂ : ∀ (v : S → ℝ) (c : ℝ), UniformBounded v → 0 ≤ c →
      ∀ s, T₂ (fun s' => v s' + c) s ≤ T₂ v s + β * c)
    {V₁ V₂ : S → ℝ} (hV₁b : UniformBounded V₁) (hV₂b : UniformBounded V₂)
    (hV₁ : ∀ s, V₁ s = T₁ V₁ s) (hV₂ : ∀ s, V₂ s = T₂ V₂ s)
    (h_op : ∀ s, T₁ V₁ s ≤ T₂ V₁ s) :
    ∀ s, V₁ s ≤ V₂ s := by
  -- `c := ⨆ s, (V₁ s − V₂ s)` is bounded above; the goal is `c ≤ 0`.
  have hbdd : BddAbove (Set.range fun s => V₁ s - V₂ s) := by
    obtain ⟨B₁, hB₁⟩ := hV₁b; obtain ⟨B₂, hB₂⟩ := hV₂b
    exact ⟨B₁ + B₂, Set.forall_mem_range.mpr fun s => by
      linarith [(abs_le.mp (hB₁ s)).2, (abs_le.mp (hB₂ s)).1]⟩
  set c := ⨆ s, (V₁ s - V₂ s) with hc
  have hc_le : ∀ s, V₁ s - V₂ s ≤ c := fun s => le_ciSup hbdd s
  set cp := max c 0 with hcp
  have hcp0 : 0 ≤ cp := le_max_right _ _
  have hV1_le : ∀ t, V₁ t ≤ V₂ t + cp := fun t => by
    have := le_trans (hc_le t) (le_max_left c 0); linarith
  have hV2cp_bdd : UniformBounded (fun t => V₂ t + cp) := by
    obtain ⟨B₂, hB₂⟩ := hV₂b
    exact ⟨B₂ + |cp|, fun t => (abs_add_le _ _).trans (add_le_add (hB₂ t) le_rfl)⟩
  -- One discounting step bounds the pointwise gap: `V₁ s − V₂ s ≤ β·cp`.
  have hstep : ∀ s, V₁ s - V₂ s ≤ β * cp := by
    intro s
    have h1 : V₁ s ≤ T₂ V₁ s := (hV₁ s).le.trans (h_op s)
    have h2 : T₂ V₁ s ≤ T₂ (fun t => V₂ t + cp) s := h_mono₂ V₁ _ hV₁b hV2cp_bdd hV1_le s
    have h3 : T₂ (fun t => V₂ t + cp) s ≤ T₂ V₂ s + β * cp := h_disc₂ V₂ cp hV₂b hcp0 s
    have h4 : T₂ V₂ s = V₂ s := (hV₂ s).symm
    linarith
  have hc_le_βcp : c ≤ β * cp := ciSup_le hstep
  -- `c ≤ β·cp` with `cp = max c 0` and `β < 1` forces `c ≤ 0`.
  have hc0 : c ≤ 0 := by
    rcases le_or_gt c 0 with h | h
    · exact h
    · exfalso
      rw [hcp, max_eq_left h.le] at hc_le_βcp
      nlinarith [mul_pos (show (0 : ℝ) < 1 - β by linarith) h]
  exact fun s => by linarith [hc_le s, hc0]

/-! ### One-sided derivatives of a max — the convex hull of branch gradients at the kink

At a tie point `f x₀ = g x₀` the max `max f g` has a convex kink: Its **right** derivative is
`max f' g'` and its **left** derivative is `min f' g'`, so the set of one-sided slopes is the
closed interval `[min f' g', max f' g']` — the convex hull of the two branch gradients (the Clarke
generalized gradient at the kink). These are pure-analysis facts about `ℝ → ℝ`; the option value
specializes them with `f = ` keep branch, `g = vOut`. -/

/-- **Right derivative of a max at a tie point.** If `f`, `g` are differentiable at `x₀` and
`f x₀ = g x₀`, then `max f g` has right derivative `max f' g'` on `[x₀, ∞)`. -/
theorem hasDerivWithinAt_max_Ici {f g : ℝ → ℝ} {f' g' x₀ : ℝ}
    (hf : HasDerivAt f f' x₀) (hg : HasDerivAt g g' x₀) (h_eq : f x₀ = g x₀) :
    HasDerivWithinAt (fun x => max (f x) (g x)) (max f' g') (Ici x₀) x₀ := by
  rw [hasDerivWithinAt_iff_tendsto_slope]
  have hsub : Ici x₀ \ {x₀} ⊆ {x₀}ᶜ := fun _ hy => hy.2
  have hfw : Tendsto (slope f x₀) (𝓝[Ici x₀ \ {x₀}] x₀) (𝓝 f') :=
    hf.tendsto_slope.mono_left (nhdsWithin_mono x₀ hsub)
  have hgw : Tendsto (slope g x₀) (𝓝[Ici x₀ \ {x₀}] x₀) (𝓝 g') :=
    hg.tendsto_slope.mono_left (nhdsWithin_mono x₀ hsub)
  refine (hfw.max hgw).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  obtain ⟨hxI, hxne⟩ := hx
  have hne' : x ≠ x₀ := by simpa using hxne
  have hxpos : 0 < x - x₀ := by
    have : x₀ < x := lt_of_le_of_ne (mem_Ici.mp hxI) (Ne.symm hne'); linarith
  simp only [slope_def_field]
  rw [h_eq, max_self]
  rcases le_total (f x) (g x) with hle | hle
  · rw [max_eq_right hle,
      max_eq_right ((div_le_div_iff_of_pos_right hxpos).mpr (by linarith))]
  · rw [max_eq_left hle,
      max_eq_left ((div_le_div_iff_of_pos_right hxpos).mpr (by linarith))]

/-- **Left derivative of a max at a tie point.** If `f`, `g` are differentiable at `x₀` and
`f x₀ = g x₀`, then `max f g` has left derivative `min f' g'` on `(-∞, x₀]`. -/
theorem hasDerivWithinAt_max_Iic {f g : ℝ → ℝ} {f' g' x₀ : ℝ}
    (hf : HasDerivAt f f' x₀) (hg : HasDerivAt g g' x₀) (h_eq : f x₀ = g x₀) :
    HasDerivWithinAt (fun x => max (f x) (g x)) (min f' g') (Iic x₀) x₀ := by
  rw [hasDerivWithinAt_iff_tendsto_slope]
  have hsub : Iic x₀ \ {x₀} ⊆ {x₀}ᶜ := fun _ hy => hy.2
  have hfw : Tendsto (slope f x₀) (𝓝[Iic x₀ \ {x₀}] x₀) (𝓝 f') :=
    hf.tendsto_slope.mono_left (nhdsWithin_mono x₀ hsub)
  have hgw : Tendsto (slope g x₀) (𝓝[Iic x₀ \ {x₀}] x₀) (𝓝 g') :=
    hg.tendsto_slope.mono_left (nhdsWithin_mono x₀ hsub)
  refine (hfw.min hgw).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  obtain ⟨hxI, hxne⟩ := hx
  have hne' : x ≠ x₀ := by simpa using hxne
  have hxneg : x - x₀ < 0 := by
    have : x < x₀ := lt_of_le_of_ne (mem_Iic.mp hxI) hne'; linarith
  simp only [slope_def_field]
  rw [h_eq, max_self]
  rcases le_total (f x) (g x) with hle | hle
  · rw [max_eq_right hle,
      min_eq_right ((div_le_div_right_of_neg hxneg).mpr (by linarith))]
  · rw [max_eq_left hle,
      min_eq_left ((div_le_div_right_of_neg hxneg).mpr (by linarith))]

/-- **Interior envelope (no kink).** Where one branch strictly dominates, `max f g` is
differentiable with that branch's derivative. This is the smooth Benveniste–Scheinkman regime,
valid off the switching locus. -/
theorem hasDerivAt_max_of_lt {f g : ℝ → ℝ} {f' x₀ : ℝ}
    (hf : HasDerivAt f f' x₀) (hg : ContinuousAt g x₀) (h : g x₀ < f x₀) :
    HasDerivAt (fun x => max (f x) (g x)) f' x₀ := by
  have hev : ∀ᶠ x in 𝓝 x₀, g x < f x := hg.eventually_lt hf.continuousAt h
  exact hf.congr_of_eventuallyEq (hev.mono fun x hx => max_eq_left hx.le)

namespace StochBudgetData

variable {n : ℕ} {A : Type*}

/-! ### The default set and its comparative statics -/

/-- The **default set** relative to a keep value `keep` and an outside option `vOut`: The states
where the outside option weakly dominates keeping. For the option value `V` the keep value is
`M.bellmanOp V`, and this is exactly the set of states where `V = vOut` (the household exercises
the outside option / forecloses). -/
def defaultSet (keep vOut : ℝ × Fin n → ℝ) : Set (ℝ × Fin n) := {st | keep st ≤ vOut st}

@[simp] lemma mem_defaultSet {keep vOut : ℝ × Fin n → ℝ} {st : ℝ × Fin n} :
    st ∈ defaultSet keep vOut ↔ keep st ≤ vOut st := Iff.rfl

/-- The default set is **antitone in the keep value**: A smaller keep value (e.g. from a tighter
collateral budget, equivalently a higher mortgage balance) enlarges the set of states where the
household defaults. -/
lemma defaultSet_antitone_keep {keep₁ keep₂ vOut : ℝ × Fin n → ℝ}
    (h : ∀ st, keep₁ st ≤ keep₂ st) : defaultSet keep₂ vOut ⊆ defaultSet keep₁ vOut :=
  fun _ hst => le_trans (h _) hst

/-- The default set is **monotone in the outside option**, *holding the keep value fixed*: A more
valuable outside option enlarges the set of states where the household defaults. (For the genuinely
recursive option value, raising `vOut` also raises the keep continuation via
`optionValueFunction_mono_of_bellmanOp_le`, so the net effect on the default set — e.g. of lower
foreclosure costs — needs the quantitative gap that the keep branch rises by at most `β` per unit;
this lemma is the fixed-keep building block, not that net statement.) -/
lemma defaultSet_mono_vOut {keep vOut₁ vOut₂ : ℝ × Fin n → ℝ}
    (h : ∀ st, vOut₁ st ≤ vOut₂ st) : defaultSet keep vOut₁ ⊆ defaultSet keep vOut₂ :=
  fun _ hst => le_trans hst (h _)

variable (M : StochBudgetData n A) (vOut : ℝ × Fin n → ℝ)

/-- On the option value's default set the value equals the outside option: `V = vOut`. -/
lemma optionValueFunction_eq_vOut_of_mem [NeZero n] [Nonempty A] {Br : ℝ}
    (hBr : ∀ a, |M.reward a| ≤ Br) (hOut : UniformBounded vOut) {st : ℝ × Fin n}
    (hst : st ∈ defaultSet (M.bellmanOp (M.optionValueFunction vOut hBr hOut)) vOut) :
    M.optionValueFunction vOut hBr hOut st = vOut st := by
  rw [M.optionValueFunction_eq_max vOut hBr hOut st]
  exact max_eq_right hst

/-- Off the option value's default set the value equals the keep branch: `V = M.bellmanOp V`. -/
lemma optionValueFunction_eq_keep_of_not_mem [NeZero n] [Nonempty A] {Br : ℝ}
    (hBr : ∀ a, |M.reward a| ≤ Br) (hOut : UniformBounded vOut) {st : ℝ × Fin n}
    (hst : st ∉ defaultSet (M.bellmanOp (M.optionValueFunction vOut hBr hOut)) vOut) :
    M.optionValueFunction vOut hBr hOut st =
      M.bellmanOp (M.optionValueFunction vOut hBr hOut) st := by
  rw [M.optionValueFunction_eq_max vOut hBr hOut st]
  exact max_eq_left (le_of_lt (not_le.mp (by simpa using hst)))

/-- **Keep operator order from budget inclusion.** If at `(v, st)` every objective feasible for
`M₁` is feasible for `M₂` (`bellmanSet` inclusion) and `M₁`'s set is nonempty, then `M₁`'s keep
value is dominated by `M₂`'s. This is how a looser budget (e.g. larger collateral headroom) raises
the keep value, the input to the option-value comparative static below. -/
lemma bellmanOp_le_of_bellmanSet_subset {M₁ M₂ : StochBudgetData n A}
    {v : ℝ × Fin n → ℝ} {st : ℝ × Fin n} {Br₂ : ℝ} (hBr₂ : ∀ a, |M₂.reward a| ≤ Br₂)
    (hv : UniformBounded v) (h_ne : (M₁.bellmanSet v st).Nonempty)
    (h_sub : M₁.bellmanSet v st ⊆ M₂.bellmanSet v st) :
    M₁.bellmanOp v st ≤ M₂.bellmanOp v st :=
  csSup_le_csSup (M₂.bellmanSet_bddAbove hBr₂ v hv st) h_ne h_sub

/-- **Option value monotone in a keep-side parameter.** If the keep value of `M₂` dominates that of
`M₁` at `M₁`'s option value (`h_op` — supplied by `bellmanOp_le_of_bellmanSet_subset` under budget
inclusion), then the whole option value rises: `V₁ ≤ V₂`. -/
theorem optionValueFunction_mono_of_bellmanOp_le [NeZero n] [Nonempty A]
    {M₁ M₂ : StochBudgetData n A} {vOut : ℝ × Fin n → ℝ}
    {Br₁ Br₂ : ℝ} (hBr₁ : ∀ a, |M₁.reward a| ≤ Br₁) (hBr₂ : ∀ a, |M₂.reward a| ≤ Br₂)
    (hOut : UniformBounded vOut)
    (h_op : ∀ st, M₁.bellmanOp (M₁.optionValueFunction vOut hBr₁ hOut) st ≤
        M₂.bellmanOp (M₁.optionValueFunction vOut hBr₁ hOut) st) :
    ∀ st, M₁.optionValueFunction vOut hBr₁ hOut st ≤ M₂.optionValueFunction vOut hBr₂ hOut st :=
  fixedPoint_le_of_operator_le (T₁ := M₁.optionBellmanOp vOut) (T₂ := M₂.optionBellmanOp vOut)
    M₂.β_lt_one
    (fun v w _ hw hvw => M₂.optionBellmanOp_monotone vOut hBr₂ v w hw hvw)
    (fun v c hv hc => M₂.optionBellmanOp_discounting vOut hBr₂ v c hv hc)
    (M₁.optionValueFunction_bounded vOut hBr₁ hOut) (M₂.optionValueFunction_bounded vOut hBr₂ hOut)
    (fun st => M₁.optionValueFunction_isFixedPt vOut hBr₁ hOut st)
    (fun st => M₂.optionValueFunction_isFixedPt vOut hBr₂ hOut st)
    (fun st => max_le_max (h_op st) le_rfl)

/-! ### Branchwise concavity

The option value `V = max(keep, vOut)` need not be globally concave: At a crossing with unequal
branch slopes the pointwise max of two concave functions has a convex kink. But on any convex
region where one branch dominates, `V` coincides with that branch, so `V` inherits the dominating
branch's concavity there. This is the precise sense in which the value is *piecewise* concave. -/

/-- **Branchwise concavity on the keep region.** On a convex set `C` where the keep branch
dominates the outside option and is concave, the option value is concave (it equals the keep branch
there). -/
theorem optionValueFunction_concaveOn_of_keep_dominant [NeZero n] [Nonempty A] {Br : ℝ}
    (hBr : ∀ a, |M.reward a| ≤ Br) (hOut : UniformBounded vOut) {C : Set ℝ} {s : Fin n}
    (h_conc : ConcaveOn ℝ C (fun w => M.bellmanOp (M.optionValueFunction vOut hBr hOut) (w, s)))
    (h_dom : ∀ w ∈ C, vOut (w, s) ≤
        M.bellmanOp (M.optionValueFunction vOut hBr hOut) (w, s)) :
    ConcaveOn ℝ C (fun w => M.optionValueFunction vOut hBr hOut (w, s)) := by
  have heq : Set.EqOn (fun w => M.bellmanOp (M.optionValueFunction vOut hBr hOut) (w, s))
      (fun w => M.optionValueFunction vOut hBr hOut (w, s)) C := fun w hw =>
    show M.bellmanOp (M.optionValueFunction vOut hBr hOut) (w, s)
        = M.optionValueFunction vOut hBr hOut (w, s) by
      rw [M.optionValueFunction_eq_max vOut hBr hOut (w, s)]; exact (max_eq_left (h_dom w hw)).symm
  exact h_conc.congr heq

/-- **Branchwise concavity on the default region.** On a convex set `C` where the outside option
dominates the keep branch and is concave, the option value is concave (it equals `vOut` there). -/
theorem optionValueFunction_concaveOn_of_vOut_dominant [NeZero n] [Nonempty A] {Br : ℝ}
    (hBr : ∀ a, |M.reward a| ≤ Br) (hOut : UniformBounded vOut) {C : Set ℝ} {s : Fin n}
    (h_conc : ConcaveOn ℝ C (fun w => vOut (w, s)))
    (h_dom : ∀ w ∈ C, M.bellmanOp (M.optionValueFunction vOut hBr hOut) (w, s) ≤ vOut (w, s)) :
    ConcaveOn ℝ C (fun w => M.optionValueFunction vOut hBr hOut (w, s)) := by
  have heq : Set.EqOn (fun w => vOut (w, s))
      (fun w => M.optionValueFunction vOut hBr hOut (w, s)) C := fun w hw =>
    show vOut (w, s) = M.optionValueFunction vOut hBr hOut (w, s) by
      rw [M.optionValueFunction_eq_max vOut hBr hOut (w, s)]; exact (max_eq_right (h_dom w hw)).symm
  exact h_conc.congr heq

/-! ### Kink-aware envelope of the option value

Specializing the generic `max`-derivative lemmas to `V = max(keep, vOut)`: Off the switching
locus `V` is differentiable with the dominant branch's derivative (smooth envelope), and at the
locus its one-sided derivatives are the `max` / `min` of the two branch derivatives (the endpoints
of the convex hull of the branch gradients). Combined with the per-branch envelopes
(`V_keep' = u'(c_keep)`, `V_fc' = u'(c_fc)`) this is the kink-aware marginal valuation of net
worth. -/

/-- `V(·, s)` is, as a function of net worth, the pointwise max of the keep branch and `vOut`. -/
lemma optionValueFunction_section_eq [NeZero n] [Nonempty A] {Br : ℝ}
    (hBr : ∀ a, |M.reward a| ≤ Br) (hOut : UniformBounded vOut) (s : Fin n) :
    (fun w => M.optionValueFunction vOut hBr hOut (w, s)) =
      fun w => max (M.bellmanOp (M.optionValueFunction vOut hBr hOut) (w, s)) (vOut (w, s)) :=
  funext fun w => M.optionValueFunction_eq_max vOut hBr hOut (w, s)

/-- **Interior keep-region envelope (smooth Benveniste–Scheinkman).** Where the keep branch
strictly dominates the outside option, `V` is differentiable in net worth with the keep branch's
derivative — the smooth envelope applies away from the switching locus. -/
theorem hasDerivAt_optionValueFunction_of_keep_gt [NeZero n] [Nonempty A] {Br : ℝ}
    (hBr : ∀ a, |M.reward a| ≤ Br) (hOut : UniformBounded vOut) {s : Fin n} {w₀ d : ℝ}
    (h_keep : HasDerivAt
      (fun w => M.bellmanOp (M.optionValueFunction vOut hBr hOut) (w, s)) d w₀)
    (h_vOut : ContinuousAt (fun w => vOut (w, s)) w₀)
    (h_gt : vOut (w₀, s) < M.bellmanOp (M.optionValueFunction vOut hBr hOut) (w₀, s)) :
    HasDerivAt (fun w => M.optionValueFunction vOut hBr hOut (w, s)) d w₀ := by
  rw [M.optionValueFunction_section_eq vOut hBr hOut s]
  exact hasDerivAt_max_of_lt h_keep h_vOut h_gt

/-- **Right derivative at the switching locus.** Where keep and the outside option tie, `V`'s right
derivative in net worth is `max` of the two branch derivatives — the upper endpoint of the convex
hull of the branch gradients. -/
theorem hasDerivWithinAt_optionValueFunction_Ici [NeZero n] [Nonempty A] {Br : ℝ}
    (hBr : ∀ a, |M.reward a| ≤ Br) (hOut : UniformBounded vOut) {s : Fin n} {w₀ dk dv : ℝ}
    (h_keep : HasDerivAt
      (fun w => M.bellmanOp (M.optionValueFunction vOut hBr hOut) (w, s)) dk w₀)
    (h_vOut : HasDerivAt (fun w => vOut (w, s)) dv w₀)
    (h_tie : M.bellmanOp (M.optionValueFunction vOut hBr hOut) (w₀, s) = vOut (w₀, s)) :
    HasDerivWithinAt (fun w => M.optionValueFunction vOut hBr hOut (w, s))
      (max dk dv) (Ici w₀) w₀ := by
  rw [M.optionValueFunction_section_eq vOut hBr hOut s]
  exact hasDerivWithinAt_max_Ici h_keep h_vOut h_tie

/-- **Left derivative at the switching locus.** Where keep and the outside option tie, `V`'s left
derivative in net worth is `min` of the two branch derivatives — the lower endpoint of the convex
hull of the branch gradients. -/
theorem hasDerivWithinAt_optionValueFunction_Iic [NeZero n] [Nonempty A] {Br : ℝ}
    (hBr : ∀ a, |M.reward a| ≤ Br) (hOut : UniformBounded vOut) {s : Fin n} {w₀ dk dv : ℝ}
    (h_keep : HasDerivAt
      (fun w => M.bellmanOp (M.optionValueFunction vOut hBr hOut) (w, s)) dk w₀)
    (h_vOut : HasDerivAt (fun w => vOut (w, s)) dv w₀)
    (h_tie : M.bellmanOp (M.optionValueFunction vOut hBr hOut) (w₀, s) = vOut (w₀, s)) :
    HasDerivWithinAt (fun w => M.optionValueFunction vOut hBr hOut (w, s))
      (min dk dv) (Iic w₀) w₀ := by
  rw [M.optionValueFunction_section_eq vOut hBr hOut s]
  exact hasDerivWithinAt_max_Iic h_keep h_vOut h_tie

end StochBudgetData

end Econlib.Optimization.DynamicProgramming
